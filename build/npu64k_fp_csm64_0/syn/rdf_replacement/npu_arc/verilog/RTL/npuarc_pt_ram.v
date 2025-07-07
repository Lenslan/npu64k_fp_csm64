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
//  File           : pt_ram.v
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
//                   memory macros needed in the ARCv2HS design. This provides a consistent
//                   interface between the CPU core and the RAMs on which it depends.
//
//  ------------------------------------------------------------------------------

`include "npuarc_pt_ramdef.v"
`include "npuarc_defines.v"
`include "npuarc_synopsys_tsmc_port_mappings.v"

module npuarc_pt_ram (
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

//Following is causing a problem when non-VDSP config is used with dev_hsdsp branch
//`ifndef npuarc_BR_PT_DATA_RANGE  
//   `define npuarc_BR_PT_DATA_RANGE 7:0
//`endif

  input                           clk;
  input [`npuarc_BR_PT_DATA_RANGE]  din;
  input [`npuarc_BR_PT_RANGE]    addr;
  input                           cs;
  input                           we;
  input   [`npuarc_BR_PT_DATA_RANGE]           wem;     // write enable mask, active high
  input                           ds;
  input                           sd;
  input 			         ls;
  output [`npuarc_BR_PT_DATA_RANGE] dout;

  wire i_ls;
     assign  i_ls = 1'b0;
 
 


 `ifdef SizeBitsExtended

     wire [7+`SizeBitsExtended:0] dout_extra; 
     wire [7+`SizeBitsExtended:0] din_extra;
     wire [7+`SizeBitsExtended:0] wem_extra;
     assign dout = dout_extra;
     assign din_extra = {{`SizeBitsExtended{1'b0}},din} ;
     assign wem_extra = {{`SizeBitsExtended{1'b0}},wem} ;
  
 `else 
  
     wire [`npuarc_BR_PT_DATA_RANGE] dout_extra; 
     wire [`npuarc_BR_PT_DATA_RANGE] din_extra;
     wire [`npuarc_BR_PT_DATA_RANGE] wem_extra;
     assign dout = dout_extra;
     assign din_extra = din ;
     assign wem_extra = wem ;

  `endif

 
  `ifdef BldCfgSizeWordsExtended
     wire [`npuarc_BR_PT_MSB+`BldCfgSizeWordsExtended:`npuarc_BR_PT_LSB] addr_extra;
     assign addr_extra = {{`BldCfgSizeWordsExtended{1'b0}},addr} ;
  `else
     wire [`npuarc_BR_PT_MSB:`npuarc_BR_PT_LSB] addr_extra;
     assign addr_extra = addr ;
  `endif


//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
 `Mempt_ram `RAM_WEM_ts07n0g41p11sadcl02ms(pt_ram0,dout_extra,addr_extra,din_extra,wem_extra,we,cs,clk,ds,sd,i_ls)
//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML
   

endmodule


`undef Mempt_ram
