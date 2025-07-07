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
//  File           : ic_data_ram.v
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
`include "npuarc_ic_data_ramdef.v"
`include "npuarc_defines.v"
`include "npuarc_synopsys_tsmc_port_mappings.v"


module npuarc_ic_data_ram (
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


  input                                    clk;
  input [`npuarc_IC_BANK_WIDTH-1:0]       din;
  input [`npuarc_IC_ADR_RANGE]            addr; 
  input                                    cs;
  input                                    we;
  input   [`npuarc_IC_BANK_BYTE_SIZE-1:0] wem; //byte enable, active high
  input                                    ds;
  input                                    sd;
  input					   ls;
  output [`npuarc_IC_BANK_WIDTH-1:0]      dout;

 wire i_ls;
     assign  i_ls = 1'b0;
 
 

   
wire   [`npuarc_IC_BANK_WIDTH-1:0]  i_wem;  // active-high bit-level write-enables

    generate
    genvar i;
 
 


 


     for (i=0; i < (`npuarc_IC_BANK_BYTE_SIZE-2); i=i+1) begin: WemGenData
        assign i_wem[8*(i+1)-1:8*i ]  = {8{wem[i]}};
	end 
     for (i=(`npuarc_IC_BANK_BYTE_SIZE-2); i < `npuarc_IC_BANK_BYTE_SIZE; i=i+1) begin: WemGenECC
        assign i_wem[(8*(`npuarc_IC_BANK_BYTE_SIZE-2))+(7*((i+1)-(`npuarc_IC_BANK_BYTE_SIZE-2)))-1:(8*(`npuarc_IC_BANK_BYTE_SIZE-2))+(7*(i-(`npuarc_IC_BANK_BYTE_SIZE-2)))]  = {7{wem[i]}};
	end 
  

  
 

    endgenerate
    



//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
`ifndef BldCfgSizeBitsDiv2 
  `Memic_data_ram `RAM_WEM_ts07n0g41p11sadcl02ms(ic_data_ram0,dout,addr,din,i_wem,we,cs,clk,ds,sd,i_ls)
   `endif
`ifdef BldCfgSizeBitsDiv2
      `Memic_data_ram `RAM_WEM_ts07n0g41p11sadcl02ms(ic_data_ram0_1,dout[`npuarc_IC_BANK_WIDTH-1:`npuarc_IC_BANK_WIDTH/2],addr,din[`npuarc_IC_BANK_WIDTH-1:`npuarc_IC_BANK_WIDTH/2],i_wem[`npuarc_IC_BANK_WIDTH-1:`npuarc_IC_BANK_WIDTH/2],we,cs,clk,ds,sd,i_ls)
      `Memic_data_ram `RAM_WEM_ts07n0g41p11sadcl02ms(ic_data_ram0_0,dout[(`npuarc_IC_BANK_WIDTH/2)-1:0],addr,din[(`npuarc_IC_BANK_WIDTH/2)-1:0],i_wem[(`npuarc_IC_BANK_WIDTH/2)-1:0],we,cs,clk,ds,sd,i_ls)
`endif

//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML

endmodule

`undef Memic_data_ram
