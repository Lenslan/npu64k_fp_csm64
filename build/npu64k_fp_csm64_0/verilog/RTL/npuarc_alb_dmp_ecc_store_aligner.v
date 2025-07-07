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
//   ALB_DMP_ECC_STORE_ALIGNER                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Read-modify-write merging in case of partial
//  stores.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_ecc_store_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_ecc_store_aligner (
  input [2:0]                    addr_r,
  input [1:0]                    size_r,
  input [`npuarc_DMP_DATA_RANGE]        wr_data_r,
  input [`npuarc_DATA_RANGE]            rd_data0,
  input [`npuarc_DATA_RANGE]            rd_data1,
  
  output reg  [`npuarc_DMP_DATA_RANGE]  wq_ecc_data0,
  output reg  [`npuarc_DMP_DATA_RANGE]  wq_ecc_data1,

  output reg [`npuarc_DMP_BE_RANGE]     wr_data0_mask,
  output reg [`npuarc_DMP_BE_RANGE]     wr_data1_mask

);

//////////////////////////////////////////////////////////////////////////////
// The following describes the working of the ecc store aligner
// rd_data0 and rd_data1 indicates the start and end of the data banks accessed
// by the partial store. Les us consider that the data_bank_sel is 0110. This
// means that Bank0 Hi and Bank1 Lo will be required by the partial store. Hence
// rd_data0 has the Bank0 Hi data and rd_data1 has the Bank1 Lo data. Let us
// consider other case, where the data_bank_sel is 1110. In this case, rd_data0
// contains the Bank0 Hi data and rd_data1 contains the Bank1 Hi data. Note that
// Bank1 Lo data will be extracted from wr_data_r.
// The wq_ecc_data0_data1_prel_PROC, does the merging of the rd_data0, rd_data1 
// and wr_data_r.
// 
//////////////////////////////////////////////////////////////////////////////

// Local declarations
//
reg [`npuarc_DMP_BE_RANGE]              size0_mask;

//reg [`DMP_BE_RANGE]              wr_data0_mask;
//reg [`DMP_BE_RANGE]              wr_data1_mask;

reg [`npuarc_DMP_DATA_RANGE]            wr_data0;
reg [`npuarc_DMP_DATA_RANGE]            wr_data1;


//////////////////////////////////////////////////////////////////////////////
//
// Size0 mask calculation
//
//////////////////////////////////////////////////////////////////////////////
// Based on the size information, mask is calculated 
// This mask will be used to calculate the masks for write data0 and data1
// 
// 
always @*
begin : size0_size1_calculation_PROC
  case (size_r)
  2'b00:   size0_mask = 8'b0000_0001; 
  2'b01:   size0_mask = 8'b0000_0011;  
  2'b10:   size0_mask = 8'b0000_1111;
  default: size0_mask = 8'b1111_1111;
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//
//  Write0, and Write1 bank mask calculation
//
//////////////////////////////////////////////////////////////////////////////
// The Size0 and size1 masks are used to calculate the read and write masks
// This will help in writing the data in the correct lane
//
always @*
begin : read_write_mask_PROC
  case (addr_r)
  3'b000:
  begin
    wr_data0      =  wr_data_r;
    wr_data0_mask =  size0_mask;

    wr_data1      =  wr_data_r;
    wr_data1_mask =  {8{1'b0}};
  end
  3'b001:
  begin
    wr_data0      =  {wr_data_r[55:0], {8{1'b0}}};
    wr_data0_mask =  {size0_mask[6:0], 1'b0};

    wr_data1      =  {{56{1'b0}}, wr_data_r[63:56]};
    wr_data1_mask =  {{7{1'b0}}, size0_mask[7]};
  end
  3'b010:
  begin
    wr_data0      =  {wr_data_r[47:0], {16{1'b0}}};
    wr_data0_mask =  {size0_mask[5:0], {2{1'b0}}};

    wr_data1      =  {{48{1'b0}}, wr_data_r[63:48]};
    wr_data1_mask =  {{6{1'b0}}, size0_mask[7:6]};
  end
  3'b011:
  begin
    wr_data0      =  {wr_data_r[39:0], {24{1'b0}}};
    wr_data0_mask =  {size0_mask[4:0], {3{1'b0}}};

    wr_data1      =  {{40{1'b0}}, wr_data_r[63:40]};
    wr_data1_mask =  {{5{1'b0}}, size0_mask[7:5]};
  end
  3'b100:
  begin
    wr_data0      =  wr_data_r;
    wr_data0_mask =  size0_mask;

    wr_data1      =  {{32{1'b0}}, wr_data_r[63:32]};
    wr_data1_mask =  {{4{1'b0}}, size0_mask[7:4]};
  end
  3'b101:
  begin
    wr_data0      =  {wr_data_r[55:0], {8{1'b0}}};
    wr_data0_mask =  {size0_mask[6:0], 1'b0};
    
    wr_data1      =  {{24{1'b0}}, wr_data_r[63:24]};
    wr_data1_mask =  {{3{1'b0}}, size0_mask[7:3]};
  end
  3'b110:
  begin
    wr_data0      =  {wr_data_r[47:0], {16{1'b0}}};
    wr_data0_mask =  {size0_mask[5:0], {2{1'b0}}};
 
    wr_data1      =  {{16{1'b0}}, wr_data_r[63:16]};
    wr_data1_mask =  {{2{1'b0}}, size0_mask[7:2]};
  end
  default:   // 3'b111:
  begin
    wr_data0      =  {wr_data_r[39:0], {24{1'b0}}};
    wr_data0_mask =  {size0_mask[4:0], {3{1'b0}}};
   
    wr_data1      =  {{8{1'b0}}, wr_data_r[63:8]};
    wr_data1_mask =  {{1{1'b0}}, size0_mask[7:1]};
  end
  endcase
end
//////////////////////////////////////////////////////////////////////////////
//
// Putting the write data in the correct lane
//
//////////////////////////////////////////////////////////////////////////////
// Step (2): To write the data in the correct lane
//
always @*
begin : wq_ecc_data0_data1_prel_PROC
  // First Byte
  //
  // Data 0
  //
  case (1'b1)
  wr_data0_mask[0]:  wq_ecc_data0[7:0] = wr_data0[7:0];
  default:           wq_ecc_data0[7:0] = rd_data0[7:0];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[0]:  wq_ecc_data1[7:0] = wr_data1[7:0];
  default:           wq_ecc_data1[7:0] = rd_data1[7:0];
  endcase
  
  // Second Byte
  //
  // Data 0 
  //
  case (1'b1)
  wr_data0_mask[1]:  wq_ecc_data0[15:8] = wr_data0[15:8];
  default:           wq_ecc_data0[15:8] = rd_data0[15:8];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[1]:  wq_ecc_data1[15:8] = wr_data1[15:8];
  default:           wq_ecc_data1[15:8] = rd_data1[15:8];
  endcase
  
  // Third Byte
  //
  // Data 0              
  //
  case (1'b1)
  wr_data0_mask[2]:  wq_ecc_data0[23:16] = wr_data0[23:16];
  default:           wq_ecc_data0[23:16] = rd_data0[23:16];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[2]:  wq_ecc_data1[23:16] = wr_data1[23:16];
  default:           wq_ecc_data1[23:16] = rd_data1[23:16];
  endcase

  // Fourth Byte
  //
  // Data 0              
  //
  case (1'b1)
  wr_data0_mask[3]:  wq_ecc_data0[31:24] = wr_data0[31:24];
  default:           wq_ecc_data0[31:24] = rd_data0[31:24];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[3]:  wq_ecc_data1[31:24] = wr_data1[31:24];
  default:           wq_ecc_data1[31:24] = rd_data1[31:24];
  endcase

  // Fifth Byte
  //
  // Data 0              
  //
  case (1'b1)
  wr_data0_mask[4]:  wq_ecc_data0[39:32] = wr_data0[39:32];
  default:           wq_ecc_data0[39:32] = rd_data1[7:0];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[4]:  wq_ecc_data1[39:32] = wr_data1[39:32];
  default:           wq_ecc_data1[39:32] = rd_data1[7:0];
  endcase
  
  // Sixth Byte
  //
  // Data 0        
  //
  case (1'b1)
  wr_data0_mask[5]:  wq_ecc_data0[47:40] = wr_data0[47:40];
  default:           wq_ecc_data0[47:40] = rd_data1[15:8];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[5]:  wq_ecc_data1[47:40] = wr_data1[47:40];
  default:           wq_ecc_data1[47:40] = rd_data1[15:8];
  endcase
    
  // Seventh Byte
  //
  // Data 0          
  //
  case (1'b1)
  wr_data0_mask[6]:  wq_ecc_data0[55:48] = wr_data0[55:48];
  default:           wq_ecc_data0[55:48] = rd_data1[23:16];
  endcase
  // Data 1
  //
  case (1'b1)
  wr_data1_mask[6]:  wq_ecc_data1[55:48] = wr_data1[55:48];
  default:           wq_ecc_data1[55:48] = rd_data1[23:16];
  endcase
    
  // Eighth Byte
  //
  // Data 0            
  //
  case (1'b1)
  wr_data0_mask[7]:  wq_ecc_data0[63:56] = wr_data0[63:56];
  default:           wq_ecc_data0[63:56] = rd_data1[31:24];
  endcase
  // Data 1
  //
  // This is not possible because during a bank cross from 1 to 0. 
  // The data1(from address1) can have information only from [6:0], due to crossing
  //  case (1'b1)
  //  wr_data1_mask[7]:  wq_ecc_data1[63:56] = wr_data1[63:56];
  wq_ecc_data1[63:56] = rd_data1[31:24];
  //  endcase
end

endmodule
