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
//  File           : scm_dbank_sram.v
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


`include "nl2_scm_dbank_sramdef.v"
//`include "nl2_defines.v"
`include "nl2_synopsys_tsmc_port_mappings.v"


module nl2_scm_dbank_sram
  #(parameter MEM_SIZE   = 1,
    parameter DATA_WIDTH = 8,
    parameter ADDR_MSB   = 0,
    parameter ADDR_LSB   = 0,
    parameter WR_SIZE    = 8,
    parameter SYNC_OUT   = 1'b1,
    parameter PIPELINED  = 1'b0)
(
    clk,
    din,
    dout,
    addr,
    regen,
    rden,
    wren,
    ds,
    sd,
    mask
  );

  input					clk;	  // clock input
  input	[DATA_WIDTH-1:0]		din;	  // write data input
  input	[ADDR_MSB:ADDR_LSB]		addr;	  // address for read or write
  input					regen;    // register enable
  input					rden;	  // memory read enable
  input					wren;	  // memory write enable
  input	[DATA_WIDTH/WR_SIZE-1:0]	mask;	  // data write enables
  output	[DATA_WIDTH-1:0]		dout;	  // read data output
  input                               ds;
  input                               sd;

  wire	[DATA_WIDTH-1:0]    		dout2;
  reg	[DATA_WIDTH-1:0]    		dout3;
  wire cs;
  assign cs = rden | wren;
  wire i_ls;
  assign  i_ls = 1'b0;

  wire [DATA_WIDTH-1:0]     i_wem;  // bit-level write-enables

  generate
  genvar i;
  for (i=0; i < ((DATA_WIDTH/WR_SIZE)-1); i=i+1) begin: WemGenData
      assign i_wem[WR_SIZE*(i+1)-1:WR_SIZE*i ]  = {WR_SIZE{mask[i]}};
  end 

  endgenerate
    
  assign i_wem[DATA_WIDTH-1:WR_SIZE*((DATA_WIDTH/WR_SIZE)-1)]  = {DATA_WIDTH-WR_SIZE*((DATA_WIDTH/WR_SIZE)-1){mask[(DATA_WIDTH/WR_SIZE)-1]}};

  always @(posedge clk)
  begin
    if (regen && PIPELINED)
      dout3 <= dout2;  
  end

  assign dout = PIPELINED ? dout3 : dout2;

  `ifdef scm_dbank_sram63
      `define scm_dbank_sram_number_of_instances 64
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-6:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire [5:0] sel;
      reg  [5:0] scm_dbank_sram_sel_q;
      wire  [DATA_WIDTH-1:0] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[ADDR_MSB-6:0];

      assign sel = addr[ADDR_MSB:ADDR_MSB-5];
    
  `elsif scm_dbank_sram31
      `define scm_dbank_sram_number_of_instances 32
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-5:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire [4:0] sel;
      reg  [4:0] scm_dbank_sram_sel_q;
      wire  [DATA_WIDTH-1:0] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[ADDR_MSB-5:0];

      assign sel = addr[ADDR_MSB:ADDR_MSB-4];    
      
  `elsif scm_dbank_sram15
      `define scm_dbank_sram_number_of_instances 16
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-4:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire [3:0] sel;
      reg  [3:0] scm_dbank_sram_sel_q;
      wire  [DATA_WIDTH-1:0] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[ADDR_MSB-4:0];

      assign sel = addr[ADDR_MSB:ADDR_MSB-3];

   `elsif scm_dbank_sram7
      `define scm_dbank_sram_number_of_instances 8
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-3:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire [2:0] sel;
      reg  [2:0] scm_dbank_sram_sel_q;
      wire [DATA_WIDTH-1:0] i_rd_data_r; 
      
      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate
	
      assign i_address = addr[ADDR_MSB-3:0];

      assign sel = addr[ADDR_MSB:ADDR_MSB-2];

   `elsif scm_dbank_sram3
      `define scm_dbank_sram_number_of_instances 4
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-2:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire [1:0] sel;
      reg  [1:0] scm_dbank_sram_sel_q;
      wire [DATA_WIDTH-1:0] i_rd_data_r; 

      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate

      assign i_address = addr[ADDR_MSB-2:0];
              
      assign sel = addr[ADDR_MSB:ADDR_MSB-1];
// Normally only powers of 2 as number of instances is supported by making  exception to support split of 12288 x128 into 3 instances of 4096x128
   `elsif scm_dbank_sram2
      `define scm_dbank_sram_number_of_instances 3
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-2:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire [1:0] sel;
      reg  [1:0] scm_dbank_sram_sel_q;
      wire [DATA_WIDTH-1:0] i_rd_data_r; 

      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate

      assign i_address = addr[ADDR_MSB-2:0];
              
      assign sel = addr[ADDR_MSB:ADDR_MSB-1];
    `elsif scm_dbank_sram1
      `define scm_dbank_sram_number_of_instances 2
      `undef scm_dbank_sram0
      wire [`scm_dbank_sram_number_of_instances-1:0] me ;
      wire [ADDR_MSB-1:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0] ;
      wire sel;
      reg  scm_dbank_sram_sel_q;
      wire [DATA_WIDTH-1:0] i_rd_data_r; 

      generate
        genvar k;
        for (k=0; k<`scm_dbank_sram_number_of_instances; k=k+1) begin: MemEn
//leda W312 off
//leda W313 off
          assign me[k] = (sel==k)?cs:1'b0;
//leda W313 on
//leda W312 on
        end
      endgenerate

      assign i_address = addr[ADDR_MSB-1:0];
              
      assign sel = addr[ADDR_MSB:ADDR_MSB];
      
    `elsif scm_dbank_sram0
      `define scm_dbank_sram_number_of_instances 1
      wire [`scm_dbank_sram_number_of_instances-1:0] me;
      wire [ADDR_MSB:0] i_address;
      wire [DATA_WIDTH-1:0] i_rd_data [`scm_dbank_sram_number_of_instances-1:0];
      wire [DATA_WIDTH-1:0] i_rd_data_r; 

      assign me[0] = cs;
      assign i_rd_data_r = i_rd_data[0];
      assign i_address = addr[ADDR_MSB:0];
 
 
      //  Assign read data output
      assign dout2 = i_rd_data_r;	     
   `endif
   
   // Read data multiplexer in case memory has multiple banks
   // Read data stays valid when CS is de-asserted.
    `ifndef scm_dbank_sram0
//leda S_1C_R off
//leda C_1406 off
//leda W396 off 
      always @(posedge clk)
       begin : scm_dbank_sram_sel_q_PROC
         if (cs == 1'b1)
           begin
             scm_dbank_sram_sel_q <= sel;
           end
        end     
//leda W396 on 
//leda C_1406 on
//leda S_1C_R on
        
      assign i_rd_data_r = i_rd_data[scm_dbank_sram_sel_q];
      //  Assign read data output
      assign dout2 = i_rd_data_r;    
    `endif
  
  
     generate
    genvar l;
    for (l=0; l<`scm_dbank_sram_number_of_instances; l=l+1) begin: scm_dbank_sram
    
     wire [DATA_WIDTH-1:0] i_rd_data_l;
     assign i_rd_data[l] = i_rd_data_l;
     wire me_l;
     assign me_l = me[l];
 
//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
`ifndef BldCfgSizeBitsDiv2 
  `ifndef BldCfgSizeBitsDiv4 
      `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l,i_rd_data_l,i_address,din,i_wem,wren,me_l,clk,ds,sd,i_ls)
     `endif
   `endif
 `ifdef BldCfgSizeBitsDiv2
    `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l_1,i_rd_data_l[DATA_WIDTH-1:DATA_WIDTH/2],i_address,din[DATA_WIDTH-1:DATA_WIDTH/2],i_wem[DATA_WIDTH-1:DATA_WIDTH/2],wren,me_l,clk,ds,sd,i_ls)
    `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l_0,i_rd_data_l[(DATA_WIDTH/2)-1:0],i_address,din[(DATA_WIDTH/2)-1:0],i_wem[(DATA_WIDTH/2)-1:0],wren,me_l,clk,ds,sd,i_ls)

`endif
`ifdef  BldCfgSizeBitsDiv4
      `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l_3,i_rd_data_l[DATA_WIDTH-1:DATA_WIDTH-(DATA_WIDTH/4)],i_address,din[DATA_WIDTH-1:DATA_WIDTH-(DATA_WIDTH/4)],i_wem[DATA_WIDTH-1:DATA_WIDTH-(DATA_WIDTH/4)],wren,me_l,clk,ds,sd,i_ls)
      `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l_2,i_rd_data_l[(3*DATA_WIDTH/4)-1:DATA_WIDTH-(DATA_WIDTH/2)],i_address,din[(3*DATA_WIDTH/4)-1:DATA_WIDTH-(DATA_WIDTH/2)],i_wem[(3*DATA_WIDTH/4)-1:DATA_WIDTH-(DATA_WIDTH/2)],wren,me_l,clk,ds,sd,i_ls)
      `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l_1,i_rd_data_l[(DATA_WIDTH/2)-1:DATA_WIDTH/4],i_address,din[(DATA_WIDTH/2)-1:DATA_WIDTH/4],i_wem[(DATA_WIDTH/2)-1:DATA_WIDTH/4],wren,me_l,clk,ds,sd,i_ls)
      `Memscm_dbank_sram `RAM_WEM_ts07n0g41p11sadcl02ms(scm_dbank_sram_l_0,i_rd_data_l[(DATA_WIDTH/4)-1:0],i_address,din[(DATA_WIDTH/4)-1:0],i_wem[(DATA_WIDTH/4)-1:0],wren,me_l,clk,ds,sd,i_ls)

`endif

      
//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML

    end
  endgenerate
  `undef scm_dbank_sram_number_of_instances
  `undef scm_dbank_sram63
  `undef scm_dbank_sram31
  `undef scm_dbank_sram15
  `undef scm_dbank_sram7
  `undef scm_dbank_sram3
  `undef scm_dbank_sram1
  `undef scm_dbank_sram0
 
endmodule


