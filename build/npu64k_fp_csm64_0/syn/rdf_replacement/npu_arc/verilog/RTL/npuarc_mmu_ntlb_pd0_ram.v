// generic RAM  (used by MMU nTLB)
//

`include "npuarc_mmu_ntlb_pd0_ramdef.v"
`include "npuarc_defines.v"
`include "npuarc_synopsys_tsmc_port_mappings.v"

module npuarc_mmu_ntlb_pd0_ram
#(parameter 
  RAM_DATA_WIDTH  = 32 + 7*(`npuarc_MMU_ECC) + (`npuarc_ALL_01_DET && `npuarc_ECC_OPTION_ADDR ),
  RAM_ADDR_WIDTH  = 7,
  RAM_DEPTH       = 128
)
(
  input                        clk,  // clock input
  input   [RAM_DATA_WIDTH-1:0] din,  // write data input
  input   [RAM_ADDR_WIDTH-1:0] addr, // address for read or write
  input                        cs,   // ME (memory enable) active high
  input                        we,   // write enable, active high
    input   			ds,  // deep sleep
  input  			sd,  // shutdown
  input ls,
  input   [`npuarc_NTLB_NUM_WAYS_ECC-1:0] wem,  // write enable mask, active high
  output  [RAM_DATA_WIDTH-1:0] dout  // read data output

);

 wire i_ls;
     assign  i_ls = 1'b0;
 
 

 
    wire [RAM_DATA_WIDTH-1:0] i_wem ;
    

 `define  p  (7+(`npuarc_ALL_01_DET && `npuarc_ECC_OPTION_ADDR ))
 
  	parameter WAY_DATA_WIDTH   = (RAM_DATA_WIDTH - (`p*`npuarc_NTLB_NUM_WAYS*1*(`npuarc_MMU_ECC)))/4;
	assign i_wem =
	  { {`p{wem[7] & wem[3]}},      // way3 ecc      
	    {WAY_DATA_WIDTH{wem[3]}},  //      data
	    {`p{wem[6] & wem[2]}},      // way2 ecc
	    {WAY_DATA_WIDTH{wem[2]}},  //      data
	    {`p{wem[5] & wem[1]}},      // way1 ecc
	    {WAY_DATA_WIDTH{wem[1]}},  //      data
	    {`p{wem[4] & wem[0]}},      // way0 ecc
	    {WAY_DATA_WIDTH{wem[0]}}   //      data
	  };



 
 
	


//Since most memory compilers

//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
  `Memmmu_ntlb_pd0_ram `RAM_WEM_ts07n0g41p11sadcl02ms(mmu_ntlb_pd0_ram0,dout,addr,din,i_wem,we,cs,clk,ds,sd,i_ls)
 
//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML
   



endmodule
`undef Memmmu_ntlb_pd0_ram
