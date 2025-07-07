//  ------------------------------------------------------------------------------
//                    Copyright Message
//  ------------------------------------------------------------------------------
//  
//  CONFIDENTIAL and PROPRIETARY
//  COPYRIGHT (c) Synopsys 2011
//
//  All rights are reserved. Reproduction in whole or in part is
//  prohibited without the written consent of the copyright owner.
//
//  ------------------------------------------------------------------------------
//                    Design Information
//  ------------------------------------------------------------------------------
//
//  File           : dc_data_ram.v
//
//  Author         : ARC
//
//  Organisation   : Synopsys / Solutions Group / Processor Solutions
//
//  Date           : $Date: 2011-05-20 04:44:45 -0700 (Fri, 20 May 2011) $
//
//  Revision       : $Revision: 130799 $
//
//
//  Description    : This is a memory macro wrapper file which interfaces the Synopsys
//                   memory macros needed in the design. This provides a consistent
//                   interface between the CPU core and the RAMs on which it depends.
//
//  ------------------------------------------------------------------------------

`include "npuarc_dc_data_ramdef.v"
`include "npuarc_defines.v"
`include "npuarc_synopsys_tsmc_port_mappings.v"

module npuarc_dc_data_ram (
    clk,
    din,
    dout,
    addr,
    cs,
    we,
    ds,
    sd,
    ls,
    wem
  );


  input                       clk;
  input [`npuarc_DC_DRAM_RANGE]      din; 
  input [`npuarc_DC_ADR_RANGE]       addr;
  input                       cs;    // Chip Select, active high
  input                       we;    // Write Enable, active high
  input  [`npuarc_DC_DBL_BE_RANGE]   wem;   // Byte Write Enable, active high
  input                               ds;
  input                               sd;
//spyglass disable_block W240
  input				      ls;
//spyglass enable_block W240
  output [`npuarc_DC_DRAM_RANGE]     dout;

  wire i_ls;
     assign  i_ls = 1'b0;
 
 


  wire    [`npuarc_DC_DRAM_RANGE] i_wem;  // active-high bit-level write-enables
    generate
    genvar i;
  


  

     for (i=0; i < `npuarc_DC_BE_SIZE; i=i+1) begin: WemGenDataLow
        assign i_wem[8*(i+1)-1:8*i ]  = {8{wem[i]}};
	end 
     for (i=(`npuarc_DC_BE_SIZE); i < `npuarc_DC_BE_ECC_SIZE; i=i+1) begin: WemGenECCLow
        assign i_wem[(8*(`npuarc_DC_BE_SIZE))+(7*((i+1)-(`npuarc_DC_BE_SIZE)))-1:(8*(`npuarc_DC_BE_SIZE))+(7*(i-(`npuarc_DC_BE_SIZE)))]  = {7{wem[i]}};
	end 
     for (i=`npuarc_DC_BE_ECC_SIZE; i < (`npuarc_DC_BE_ECC_SIZE+`npuarc_DC_BE_SIZE); i=i+1) begin: WemGenDataHigh
        assign i_wem[8*(i+1)-(`npuarc_DC_BE_ECC_SIZE-`npuarc_DC_BE_SIZE)-1:8*i-(`npuarc_DC_BE_ECC_SIZE-`npuarc_DC_BE_SIZE) ]  = {8{wem[i]}};
	end 
     for (i=(`npuarc_DC_BE_ECC_SIZE+`npuarc_DC_BE_SIZE); i < `npuarc_DC_DBL_BE_SIZE; i=i+1) begin: WemGenECCHigh
        assign i_wem[(8*(`npuarc_DC_BE_ECC_SIZE+`npuarc_DC_BE_SIZE))+(7*((i+1)-(`npuarc_DC_BE_ECC_SIZE+`npuarc_DC_BE_SIZE)))-(`npuarc_DC_BE_ECC_SIZE-`npuarc_DC_BE_SIZE)-1:(8*(`npuarc_DC_BE_ECC_SIZE+`npuarc_DC_BE_SIZE))+(7*(i-(`npuarc_DC_BE_ECC_SIZE+`npuarc_DC_BE_SIZE)))-(`npuarc_DC_BE_ECC_SIZE-`npuarc_DC_BE_SIZE)]  = {7{wem[i]}};
	end 
  
  


    endgenerate
    
    


//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
  `Memdc_data_ram `RAM_WEM_ts07n0g41p11sadcl02ms(dc_data_ram0,dout,addr,din,i_wem,we,cs,clk,ds,sd,i_ls)
//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML
  
endmodule
`undef  Memdc_data_ram

