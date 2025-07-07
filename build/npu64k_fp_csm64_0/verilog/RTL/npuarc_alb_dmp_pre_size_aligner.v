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
//   ALB_DMP_PRE_SIZE_ALIGNER                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module translates the incoming size information to size0 and size1 
//  information,based on the data bank selection information.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_pre_size_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_pre_size_aligner (
  input [2:0]                    addr_2_to_0,
  input [1:0]                    size,
  input [3:0]                    bank_sel,

  output reg [2:0]               aln_size0,
  output reg [2:0]               aln_size1
);


// Local declarations
//
reg [2:0]                        aln_size0_prel;

wire                             word;
wire                             dword;

//////////////////////////////////////////////////////////////////////////////
// Size table
//
//////////////////////////////////////////////////////////////////////////////
//                         |
//        Size[2:0]        |           Read Value
//-------------------------|-------------------------------------------------
//          000            |             1 - Byte
//          001            |             2 - Bytes (Half Word)
//          010            |             4 - Bytes (Word)
//          011            |             8 - Bytes (Double Word)
//          100            |             3 - Bytes
//          101            |             5 - Bytes
//          110            |             6 - Bytes      
//          111            |             7 - Bytes
//////////////////////////////////////////////////////////////////////////////


assign dword = size[0];
assign word  = size[1];



//////////////////////////////////////////////////////////////////////////////
// Size0, Size1  calculation  
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : aln_size1_PROC 

  case ({addr_2_to_0})
  3'b001:  
  begin
    aln_size0_prel  = 3'b111;
    aln_size1       = 3'b000;
  end  
  
  3'b010:  
  begin
    aln_size0_prel  = 3'b110;
    aln_size1       = 3'b001;
  end  
  
  3'b011:  
  begin
    aln_size0_prel  = 3'b101;
    aln_size1       = 3'b100;
  end  
  
  3'b100:  
  begin
    aln_size0_prel  = 3'b010;
    aln_size1       = 3'b010;
  end
    
  3'b101:
  begin
    aln_size0_prel  = 3'b100;
    
    casez ({dword,word})
    2'b1?:
    begin
      //  Double Word
      aln_size1     = 3'b101;
    end
    default: // 2'b0?:
    begin
      //  Word
      aln_size1     = 3'b000;
    end
    endcase
  end
  3'b110:
  begin
    aln_size0_prel  = 3'b001;
    
    casez ({dword,word})
    2'b1?:
    begin
      //  Double Word
      aln_size1     = 3'b110;
    end
    default: // 2'b0?:
    begin
      //  Word
      aln_size1     = 3'b001;
    end
    endcase
  end
  default: // 3'b111:
  begin
    aln_size0_prel  = 3'b000;
    
    casez ({word,dword})
    2'b0?:
    begin
      //  Half Word
      aln_size1     = 3'b000;
    end
    2'b10:
    begin
      //  Word
      aln_size1     = 3'b100;
    end
    default: // 2'b11:
    begin
      //  Double Word
      aln_size1     = 3'b111;
    end
    endcase
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Adjust size0 accordinlgy
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aln_size0_PROC 

  if (  bank_sel[3] 
      & bank_sel[0])
  begin
    // odd to even crossing
    //
    aln_size0 = aln_size0_prel;
  end
  else
  begin
    // No odd to even crossing
    //
    aln_size0 = {1'b0, size};
  end
end

endmodule
