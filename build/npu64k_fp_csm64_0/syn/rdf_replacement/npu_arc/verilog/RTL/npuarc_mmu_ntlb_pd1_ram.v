// leda on


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// NTLB PD1 (data) ram                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
 
// leda off

// generic RAM  (used by MMU nTLB)
//

`include "npuarc_mmu_ntlb_pd1_ramdef.v"
`include "npuarc_defines.v"
`include "npuarc_synopsys_tsmc_port_mappings.v"

module npuarc_mmu_ntlb_pd1_ram
#(parameter 
  RAM_DATA_WIDTH  = 32,
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
  input				ls,   //light sleep
  output  [RAM_DATA_WIDTH-1:0] dout  // read data output

);

  wire i_ls;
     assign  i_ls = 1'b0;
 
 


//spyglass disable_block UndrivenInTerm-ML
//spyglass disable_block WarnAnalyzeBBox
//spyglass disable_block STARC-1.6.6.3
//leda NTL_CON08 off
//leda NTL_CON12 off
//leda WV951025 off
  `Memmmu_ntlb_pd1_ram `RAM_ts07n0g41p11sadcl02ms(mmu_ntlb_pd1_ram0,dout,addr,din,we,cs,clk,ds,sd,i_ls)
//leda WV951025 on
//leda NTL_CON12 on
//leda NTL_CON08 on
//spyglass enable_block STARC-1.6.6.3
//spyglass enable_block WarnAnalyzeBBox
//spyglass enable_block UndrivenInTerm-ML
   


endmodule
`undef Memmmu_ntlb_pd1_ram
