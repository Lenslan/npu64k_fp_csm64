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
//  File           : dccm_ram.v
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


`include "npuarc_dccm_ramdef.v"
`include "npuarc_defines.v"
`include "npuarc_synopsys_tsmc_port_mappings.v"


module npuarc_dccm_ram (
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
  input [`npuarc_DCCM_DRAM_RANGE]    din;
  input [`npuarc_DCCM_ADDR_RANGE]    addr; 
  input                       cs;           // Chip Select, active high
  input                       we;           // Write Enable, active high
  input [`npuarc_DCCM_BE_RANGE]      wem;          // Byte Write Enable, active high
  input                               ds;
  input                               sd;
//spyglass disable_block W240
  input				      ls;
//spyglass enable_block W240
  output [`npuarc_DCCM_DRAM_RANGE]   dout;


 wire i_ls;
     assign  i_ls = 1'b0;
 
 

  wire [`npuarc_DCCM_DRAM_RANGE]     i_wem;  // bit-level write-enables
  `ifdef SizeBitsExtended
  wire [`npuarc_DCCM_DRAM_MSB+`SizeBitsExtended:0]     din_extra;  // bit-level write-enables
  wire [`npuarc_DCCM_DRAM_MSB+`SizeBitsExtended:0]     wem_extra;  // bit-level write-enables

  assign din_extra = {{`SizeBitsExtended{1'b0}},din} ;
  assign wem_extra = {{`SizeBitsExtended{1'b0}},i_wem} ;
  `else
  wire [`npuarc_DCCM_DRAM_RANGE]     din_extra;  // bit-level write-enables
  wire [`npuarc_DCCM_DRAM_RANGE]     wem_extra;  // bit-level write-enables

  assign din_extra = din ;
  assign wem_extra = i_wem ;
  `endif

    generate
    genvar i;
  
  
   if  (`npuarc_DCCM_MEM_BANKS == 4 || `npuarc_DCCM_MEM_BANKS == 8)
    begin
     for (i=0; i < (`npuarc_DCCM_BE_BITS-1); i=i+1) begin: WemGenData32
        assign i_wem[8*(i+1)-1:8*i ]  = {8{wem[i]}};
	end 
     for (i=(`npuarc_DCCM_BE_BITS-1); i < `npuarc_DCCM_BE_BITS; i=i+1) begin: WemGenECC32
        assign i_wem[(8*(`npuarc_DCCM_BE_BITS-1))+(7*((i+1)-(`npuarc_DCCM_BE_BITS-1)))-1:(8*(`npuarc_DCCM_BE_BITS-1))+(7*(i-(`npuarc_DCCM_BE_BITS-1)))]  = {7{wem[i]}};
	end
    end	
	
   else 	 
    begin
       for (i=0; i < ((`npuarc_DCCM_BE_BITS)/2 -1); i=i+1) begin: WemGenData32
        assign i_wem[8*(i+1)-1:8*i ]  = {8{wem[i]}};
	end     
     for (i=((`npuarc_DCCM_BE_BITS/2-1)); i < `npuarc_DCCM_BE_BITS/2; i=i+1) begin: WemGenECC32
        assign i_wem[((8*i)+6):(8*i)]  = {7{wem[i]}};
	end 	
	
     for (i=(`npuarc_DCCM_BE_BITS/2); i < (`npuarc_DCCM_BE_BITS-1); i=i+1) begin: WemGenData64
        assign i_wem[((8*i)+6):(8*i)-1]  = {8{wem[i]}};
	end 

     for (i=((`npuarc_DCCM_BE_BITS-1)); i < `npuarc_DCCM_BE_BITS; i=i+1) begin: WemGenECC64
        assign i_wem[((8*i)+5):(8*i)-1]  = {7{wem[i]}};
	end  
    
     
   end
  


  

    endgenerate
    
  `ifdef dccm_ram63
//      `define dccm_ram_number_of_instances 64
      `undef dccm_ram0
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me ;
      wire [`npuarc_DCCM_ADDR_MSB-6:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0] ;
      wire [5:0] sel;
      reg  [5:0] dccm_sel_q;
      wire  [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`npuarc_dccm_ram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[`npuarc_DCCM_ADDR_MSB-6:0];

      assign sel = addr[`npuarc_DCCM_ADDR_MSB:`npuarc_DCCM_ADDR_MSB-5];
    
  `elsif dccm_ram31
//      `define dccm_ram_number_of_instances 32
      `undef dccm_ram0
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me ;
      wire [`npuarc_DCCM_ADDR_MSB-5:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0] ;
      wire [4:0] sel;
      reg  [4:0] dccm_sel_q;
      wire  [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`npuarc_dccm_ram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[`npuarc_DCCM_ADDR_MSB-5:0];

      assign sel = addr[`npuarc_DCCM_ADDR_MSB:`npuarc_DCCM_ADDR_MSB-4];    
      
  `elsif dccm_ram15
//      `define dccm_ram_number_of_instances 16
      `undef dccm_ram0
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me ;
      wire [`npuarc_DCCM_ADDR_MSB-4:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0] ;
      wire [3:0] sel;
      reg  [3:0] dccm_sel_q;
      wire  [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`npuarc_dccm_ram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[`npuarc_DCCM_ADDR_MSB-4:0];

      assign sel = addr[`npuarc_DCCM_ADDR_MSB:`npuarc_DCCM_ADDR_MSB-3];

   `elsif dccm_ram7
//      `define dccm_ram_number_of_instances 8
      `undef dccm_ram0
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me ;
      wire [`npuarc_DCCM_ADDR_MSB-3:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0] ;
      wire [2:0] sel;
      reg  [2:0] dccm_sel_q;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`npuarc_dccm_ram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[`npuarc_DCCM_ADDR_MSB-3:0];

      assign sel = addr[`npuarc_DCCM_ADDR_MSB:`npuarc_DCCM_ADDR_MSB-2];

   `elsif dccm_ram3
//      `define dccm_ram_number_of_instances 4
      `undef dccm_ram0
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me ;
      wire [`npuarc_DCCM_ADDR_MSB-2:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0] ;
      wire [1:0] sel;
      reg  [1:0] dccm_sel_q;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 

      generate
        genvar k;
        for (k=0; k<`npuarc_dccm_ram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate

      assign i_address = addr[`npuarc_DCCM_ADDR_MSB-2:0];
              
      assign sel = addr[`npuarc_DCCM_ADDR_MSB:`npuarc_DCCM_ADDR_MSB-1];

    `elsif dccm_ram1
//      `define dccm_ram_number_of_instances 2
      `undef dccm_ram0
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me ;
      wire [`npuarc_DCCM_ADDR_MSB-1:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0] ;
      wire sel;
      reg  dccm_sel_q;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 

      generate
        genvar k;
        for (k=0; k<`npuarc_dccm_ram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate

      assign i_address = addr[`npuarc_DCCM_ADDR_MSB-1:0];
              
      assign sel = addr[`npuarc_DCCM_ADDR_MSB:`npuarc_DCCM_ADDR_MSB];
      
    `elsif dccm_ram0
//      `define dccm_ram_number_of_instances 1
      wire [`npuarc_dccm_ram_number_of_instances-1:0] me;
      wire [`npuarc_DCCM_ADDR_MSB:0] i_address;
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data [`npuarc_dccm_ram_number_of_instances-1:0];
      wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data_r; 

      assign me[0] = cs;
      assign i_rd_data_r = i_rd_data[0];
      assign i_address = addr[`npuarc_DCCM_ADDR_MSB:0];
 
 
      //  Assign read data output
      assign dout = i_rd_data_r;	     
   `endif
   
   // Read data multiplexer in case memory has multiple banks
   // Read data stays valid when CS is de-asserted.
    `ifndef dccm_ram0
//leda S_1C_R off
//leda C_1406 off
//leda W396 off 
      always @(posedge clk)
       begin : dccm_sel_q_PROC
         if (cs == 1'b1)
           begin
             dccm_sel_q <= sel;
           end
        end     
//leda W396 on 
//leda C_1406 on
//leda S_1C_R on
        
      assign i_rd_data_r = i_rd_data[dccm_sel_q];
      //  Assign read data output
      assign dout = i_rd_data_r;    
    `endif
  
  
     generate
    genvar l;
    for (l=0; l<`npuarc_dccm_ram_number_of_instances; l=l+1) begin: DCCM
    
  `ifdef SizeBitsExtended
     wire [`npuarc_DCCM_DRAM_MSB+`SizeBitsExtended:0]     i_rd_data_l;  // bit-level write-enables
     assign i_rd_data[l] = i_rd_data_l[`npuarc_DCCM_DRAM_RANGE];
  `else
     wire [`npuarc_DCCM_DRAM_RANGE] i_rd_data_l;
     assign i_rd_data[l] = i_rd_data_l;
  `endif
     wire me_l;
     assign me_l = me[l];
 
//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
    `Memdccm_ram `RAM_WEM_ts07n0g41p11sadcl02ms(dccm_ram_l,i_rd_data_l,i_address,din_extra,wem_extra,we,me_l,clk,ds,sd,i_ls)
//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML

    end
  endgenerate
 
  
endmodule

  `undef dccm_ram63
  `undef dccm_ram31
  `undef dccm_ram15
  `undef dccm_ram7
  `undef dccm_ram3
  `undef dccm_ram1
  `undef dccm_ram0
  `undef Memdccm_ram
  `undef npuarc_dccm_ram_number_of_instances
