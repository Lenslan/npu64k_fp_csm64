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
//   ALB_DMP_MASK_ALIGNER                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the data mask information required during the store
//  operation. This selectively enable the bytes that are to be written during
//  the store operation.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_mask_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_mask_aligner (
  input [2:0]                    size,
  input [3:0]                    addr_3_to_0,
  input                          valid_r,
    
  output reg [7:0]               bank0_mask,   // hi-lo
  output reg [7:0]               bank1_mask    // hi-lo

);

// Local declarations
//
reg [22:0]  mask_aligned;
reg [22:0]  byte_mask_aligned;
reg [22:0]  mask_aligned_1b;
reg [22:0]  mask_aligned_2b;
reg [22:0]  mask_aligned_3b;
reg [22:0]  mask_aligned_4b;
reg [22:0]  mask_aligned_5b;
reg [22:0]  mask_aligned_6b;
reg [22:0]  mask_aligned_7b;
reg [22:0]  mask_aligned_8b;

reg [3:0]   s0;
reg [3:0]   s1;
reg [3:0]   s2;
reg [3:0]   s3;
reg [3:0]   s4;
reg [3:0]   s5;
reg [3:0]   s6;
reg [3:0]   s7;
reg [3:0]   s8;
reg [3:0]   s9;
reg [3:0]   s10;
reg [3:0]   s11;
reg [3:0]   s12;
reg [3:0]   s13;
reg [3:0]   s14;
reg [3:0]   s15;
reg [15:0]  addr_3_to_0_hot;

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  bit vector          
// Optimized logic to detect when (src1 + src2 == Ki), with src2 being zero 
//////////////////////////////////////////////////////////////////////////
always @*
begin : addr_3_to_0_hot_PROC
  s0                 = addr_3_to_0  ^ 4'd15;
  addr_3_to_0_hot[0] = & s0 & valid_r;
  
  s1                 = addr_3_to_0  ^ 4'd14;
  addr_3_to_0_hot[1] = & s1 & valid_r;
  
  s2                 = addr_3_to_0  ^ 4'd13;
  addr_3_to_0_hot[2] = & s2 & valid_r;
  
  s3                 = addr_3_to_0  ^ 4'd12;
  addr_3_to_0_hot[3] = & s3 & valid_r;
  
  s4                 = addr_3_to_0  ^ 4'd11;
  addr_3_to_0_hot[4] = & s4 & valid_r;
  
  s5                 = addr_3_to_0  ^ 4'd10;
  addr_3_to_0_hot[5] = & s5 & valid_r;
  
  s6                 = addr_3_to_0  ^ 4'd9;
  addr_3_to_0_hot[6] = & s6 & valid_r;
  
  s7                 = addr_3_to_0  ^ 4'd8;
  addr_3_to_0_hot[7] = & s7 & valid_r;
  
  s8                 = addr_3_to_0  ^ 4'd7;
  addr_3_to_0_hot[8] = & s8 & valid_r;
  
  s9                 = addr_3_to_0  ^ 4'd6;
  addr_3_to_0_hot[9] = & s9 & valid_r;
  
  s10                 = addr_3_to_0  ^ 4'd5;
  addr_3_to_0_hot[10] = & s10 & valid_r;
  
  s11                 = addr_3_to_0  ^ 4'd4;
  addr_3_to_0_hot[11] = & s11 & valid_r;
  
  s12                 = addr_3_to_0  ^ 4'd3;
  addr_3_to_0_hot[12] = & s12 & valid_r;
  
  s13                 = addr_3_to_0  ^ 4'd2;
  addr_3_to_0_hot[13] = & s13 & valid_r;
  
  s14                 = addr_3_to_0  ^ 4'd1;
  addr_3_to_0_hot[14] = & s14 & valid_r;
  
  s15                 = addr_3_to_0  ^ 4'd0;
  addr_3_to_0_hot[15] = & s15 & valid_r;
  
end


//////////////////////////////////////////////////////////////////////////////
// 
// Byte  Mask pre-computation
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : pre_byte_mask_aligned_PROC 
  byte_mask_aligned = { {7{1'b0}}, addr_3_to_0_hot};
end

always @*
begin : mask_aligned_PROC
  mask_aligned_1b   =   byte_mask_aligned;
  
  mask_aligned_2b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0};
  
  mask_aligned_3b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0}
                      | {byte_mask_aligned[20:0], 2'b00};
  
  mask_aligned_4b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0}
                      | {byte_mask_aligned[20:0], 2'b00}
                      | {byte_mask_aligned[19:0], 3'b000};
 
  mask_aligned_5b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0}
                      | {byte_mask_aligned[20:0], 2'b00}
                      | {byte_mask_aligned[19:0], 3'b000}
                      | {byte_mask_aligned[18:0], 4'b0000};
  
  mask_aligned_6b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0}
                      | {byte_mask_aligned[20:0], 2'b00}
                      | {byte_mask_aligned[19:0], 3'b000}
                      | {byte_mask_aligned[18:0], 4'b0000}
                      | {byte_mask_aligned[17:0], 5'b00000};
  
  mask_aligned_7b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0}
                      | {byte_mask_aligned[20:0], 2'b00}
                      | {byte_mask_aligned[19:0], 3'b000}
                      | {byte_mask_aligned[18:0], 4'b0000}
                      | {byte_mask_aligned[17:0], 5'b00000}
                      | {byte_mask_aligned[16:0], 6'b000000};
  
  mask_aligned_8b   =   byte_mask_aligned
                      | {byte_mask_aligned[21:0], 1'b0}
                      | {byte_mask_aligned[20:0], 2'b00}
                      | {byte_mask_aligned[19:0], 3'b000}
                      | {byte_mask_aligned[18:0], 4'b0000}
                      | {byte_mask_aligned[17:0], 5'b00000}
                      | {byte_mask_aligned[16:0], 6'b000000}
                      | {byte_mask_aligned[15:0], 7'b0000000};
end

//////////////////////////////////////////////////////////////////////////////
// 
// Byte  Mask computation
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : byte_mask_aligned_PROC 

  case (size)
  3'b000:   // 1-byte
  begin
    mask_aligned = mask_aligned_1b;
  end
  
  3'b001:   // 2-bytes (half)
  begin
    mask_aligned = mask_aligned_2b;
  end
  
  3'b100:   // 3- Bytes
  begin
    mask_aligned = mask_aligned_3b;
  end

  3'b010:   // 4- bytes (word)
  begin
    mask_aligned = mask_aligned_4b;
  end
  
  3'b101:   // 5- Bytes
  begin
    mask_aligned = mask_aligned_5b;
  end

  3'b110:   // 6- Bytes
  begin
    mask_aligned = mask_aligned_6b;
  end

  3'b111:   // 7- Bytes
  begin
    mask_aligned = mask_aligned_7b;
  end

  3'b011: // 8-bytes (double word)
  begin
    mask_aligned = mask_aligned_8b;
  end
  default:
  begin
    mask_aligned = {23{1'b0}};
  end
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
// 
// Asynchronous logic for the mask alignement
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : bank_mask_PROC
  if (~addr_3_to_0[3])
  begin
    // address < 8
    //
    bank0_mask = mask_aligned[7:0];
    bank1_mask = mask_aligned[15:8];
  end
  else
  begin
    // address >= 8
    //
    bank1_mask = mask_aligned[15:8];
    bank0_mask = {1'b0, mask_aligned[22:16]};
  end
end

endmodule // alb_dmp_mask_aligner
