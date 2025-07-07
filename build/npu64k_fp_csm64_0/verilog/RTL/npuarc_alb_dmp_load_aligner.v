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
//  #####   #    #  #####           #        ####     ##    #####
//  #    #  ##  ##  #    #          #       #    #   #  #   #    #
//  #    #  # ## #  #    #          #       #    #  #    #  #    #
//  #    #  #    #  #####           #       #    #  ######  #    #
//  #    #  #    #  #               #       #    #  #    #  #    #
//  #####   #    #  #      #######  ######   ####   #    #  #####  #######
//
//        ##    #        #     ####   #    #  ######  #####
//       #  #   #        #    #    #  ##   #  #       #    #
//      #    #  #        #    #       # #  #  #####   #    #
//      ######  #        #    #  ###  #  # #  #       #####
//      #    #  #        #    #    #  #   ##  #       #   #
//      #    #  ######   #     ####   #    #  ######  #    #
//
// ===========================================================================
//
// Description:
//
//  The dmp_load_aligner module implements the alignment logic for the
//  load-side of the Data Memory Pipeline (DMP).
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_load_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_load_aligner (
  input [`npuarc_DOUBLE_RANGE]         dmp_aln_data0,
  input [`npuarc_DOUBLE_RANGE]         dmp_aln_data1,
  input [1:0]                   dmp_aln_size,
  input                         dmp_aln_sex,
  input [3:0]                   dmp_aln_addr_3_to_0,

  output[`npuarc_DMP_DATA_RANGE]       aln_data    
);

// Local Declarations

reg [`npuarc_DOUBLE_RANGE] aln_data_prel;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variable are not used in certain configurations
reg [`npuarc_DOUBLE_RANGE] aln_data_sex; 
wire [191:0]        data_prel;
// leda NTL_CON13A on
///////////////////////////////////////////////////////////////////////////////
// Process to align the data according to the size and and the sex
//
//////////////////////////////////////////////////////////////////////////////

assign data_prel = {dmp_aln_data0, dmp_aln_data1, dmp_aln_data0};

always @*
begin : align_data_PROC
  //
  // Always take 64 bit data from the start address
  // the aln_data_sex_PROC will take care of the aln_size
  //
  aln_data_prel[63:0]  = data_prel[dmp_aln_addr_3_to_0*8+:64];
end

////////////////////////////////////////////////////////////////////////////////
//
// Sign Extension
//
///////////////////////////////////////////////////////////////////////////////
always @*
begin : aln_data_sex_PROC
  casez (dmp_aln_size)
  2'b00:
  begin
    aln_data_sex =   (dmp_aln_sex) 
                   ? { {56{aln_data_prel[7]}},aln_data_prel[`npuarc_BYTE0_RANGE]}
                   : { {56{1'b0}},            aln_data_prel[7:0]}; 
  end
  2'b01:
  begin
    aln_data_sex =   (dmp_aln_sex)
                   ? { {48{aln_data_prel[15]}},aln_data_prel[`npuarc_HBYTE0_RANGE]}
                   : { {48{1'b0}},             aln_data_prel[`npuarc_HBYTE0_RANGE]};  
  end
  2'b10:
  begin
    aln_data_sex = aln_data_prel;  
  end
  default: // 2'b11:
  begin
    aln_data_sex = aln_data_prel;  
  end
  endcase
end  
  

////////////////////////////////////////////////////////////////////////////////
// Output driver
//
///////////////////////////////////////////////////////////////////////////////
assign aln_data = aln_data_sex[`npuarc_DMP_DATA_RANGE];
   
endmodule // alb_dmp_load_aligner
