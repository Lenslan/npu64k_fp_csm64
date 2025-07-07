// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.


// This file was automatically generated.
// Includes found in dependent files:
`include "const.def"
`include "npuarc_cc_exported_defines.v"
`include "npuarc_cc_defines.v"
`include "npuarc_biu_defines.v"
`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_archipelago(
    input  [3:0] cbu_axi_rid             //  <   alb_mss_fab
  , input  cbu_axi_arready               //  <   alb_mss_fab
  , input  cbu_axi_rvalid                //  <   alb_mss_fab
  , input  [63:0] cbu_axi_rdata          //  <   alb_mss_fab
  , input  [1:0] cbu_axi_rresp           //  <   alb_mss_fab
  , input  cbu_axi_rlast                 //  <   alb_mss_fab
  , input  [3:0] cbu_axi_bid             //  <   alb_mss_fab
  , input  cbu_axi_awready               //  <   alb_mss_fab
  , input  cbu_axi_wready                //  <   alb_mss_fab
  , input  cbu_axi_bvalid                //  <   alb_mss_fab
  , input  [1:0] cbu_axi_bresp           //  <   alb_mss_fab
  , input  sccm_axi_arvalid              //  <   alb_mss_fab
  , input  [15:0] sccm_axi_arid          //  <   alb_mss_fab
  , input  [23:0] sccm_axi_araddr        //  <   alb_mss_fab
  , input  [1:0] sccm_axi_arregion       //  <   alb_mss_fab
  , input  [1:0] sccm_axi_arburst        //  <   alb_mss_fab
  , input  [3:0] sccm_axi_arlen          //  <   alb_mss_fab
  , input  [2:0] sccm_axi_arsize         //  <   alb_mss_fab
  , input  sccm_axi_rready               //  <   alb_mss_fab
  , input  sccm_axi_awvalid              //  <   alb_mss_fab
  , input  [15:0] sccm_axi_awid          //  <   alb_mss_fab
  , input  [23:0] sccm_axi_awaddr        //  <   alb_mss_fab
  , input  [1:0] sccm_axi_awregion       //  <   alb_mss_fab
  , input  [1:0] sccm_axi_awburst        //  <   alb_mss_fab
  , input  [3:0] sccm_axi_awlen          //  <   alb_mss_fab
  , input  [2:0] sccm_axi_awsize         //  <   alb_mss_fab
  , input  sccm_axi_wvalid               //  <   alb_mss_fab
  , input  [63:0] sccm_axi_wdata         //  <   alb_mss_fab
  , input  [7:0] sccm_axi_wstrb          //  <   alb_mss_fab
  , input  sccm_axi_wlast                //  <   alb_mss_fab
  , input  sccm_axi_bready               //  <   alb_mss_fab
  , input  mbus_clk_en                   //  <   alb_mss_clkctrl
  , input  dbus_clk_en                   //  <   alb_mss_clkctrl
  , input  clk                           //  <   alb_mss_clkctrl
// spyglass disable_block Reset_info09a
// SMD: reset net is unconstrained
// SJ:  
  , input  rst_a                         //  <   io_pad_ring
// spyglass enable_block Reset_info09a
  , input  [7:0] clusternum              //  <   io_pad_ring
  , input  test_mode                     //  <   io_pad_ring
// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  arc_event_a                   //  <   io_pad_ring
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  arc_halt_req_a                //  <   io_pad_ring
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  arc_run_req_a                 //  <   io_pad_ring
// spyglass enable_block Ac_coherency06

  , input  [95:0] EventManager_evm_event_a //  <   apex_testbench.EventManager_tb
  , input  EventManager_evm_sleep        //  <   apex_testbench.EventManager_tb
// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq17_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq19_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq21_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq22_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq23_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq24_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq25_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq26_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq27_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq28_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq29_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq30_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq31_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq32_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq33_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq34_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq35_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq36_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq37_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq38_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq39_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq40_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq41_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq42_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq43_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq44_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq45_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq46_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq47_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq48_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq49_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq50_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq51_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq52_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq53_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  irq54_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

  , input  [21:0] intvbase_in            //  <   io_pad_ring
  , input  dbg_cmdval                    //  <   fast_rascal
  , input  dbg_eop                       //  <   fast_rascal
  , input  [31:0] dbg_address            //  <   fast_rascal
  , input  [3:0] dbg_be                  //  <   fast_rascal
  , input  [1:0] dbg_cmd                 //  <   fast_rascal
  , input  [31:0] dbg_wdata              //  <   fast_rascal
  , input  dbg_rspack                    //  <   fast_rascal
  , input  dbg_prot_sel                  //  <   fast_rascal
  , input  pclkdbg_en                    //  <   clock_and_reset
// spyglass disable_block Propagate_Resets
// SMD: Reset is not propogated in the design
// SJ: Info not a warning. No potentially issues. Presetdbgn is propogated and used internally in APB Debug files 

  , input  presetdbgn                    //  <   clock_and_reset
// spyglass enable_block Propagate_Resets
  , input  [31:2] paddrdbg               //  <   fast_rascal
  , input  pseldbg                       //  <   fast_rascal
  , input  penabledbg                    //  <   fast_rascal
  , input  pwritedbg                     //  <   fast_rascal
  , input  [31:0] pwdatadbg              //  <   fast_rascal
  , input  dbgen                         //  <   fast_rascal
  , input  niden                         //  <   fast_rascal
// spyglass disable_block Ac_coherency06
// SMD: Unsynchronized Crossing
// SJ:  
  , input  dbg_cache_rst_disable         //  <   alb_mss_ext_stub
// spyglass enable_block Ac_coherency06

  , input  dccm_dmi_priority             //  <   alb_mss_ext_stub
// spyglass disable_block Ac_conv04
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  [7:0] arcnum /* verilator public_flat */ //  <   io_pad_ring
// spyglass enable_block Ac_conv04
  , input  wdt_clk                       //  <   alb_mss_clkctrl
  , input  wdt_ext_timeout_ack_r         //  <   alb_mss_ext_stub
  , input  mem_ds                        //  <   alb_mss_ext_stub
  , input  mem_sd                        //  <   alb_mss_ext_stub
  , input  rtt_clk                       //  <   alb_mss_clkctrl
  , input  atclken                       //  <   rtt_testbench
// spyglass disable_block Propagate_Resets
// SMD: Reset not propagated
// SJ:  Non-issue, RTL behaving as expected
  , input  atresetn                      //  <   rtt_testbench
// spyglass enable_block Propagate_Resets
  , input  [63:0] atb_cstimestamp        //  <   rtt_csts_gen
  , input  atready                       //  <   rtt_testbench
  , input  afvalid                       //  <   rtt_testbench
  , input  syncreq                       //  <   rtt_testbench
  , input  cti_trace_start               //  <   rtt_cti_stub
  , input  cti_trace_stop                //  <   rtt_cti_stub
  , input  [31:2] arct0_paddrdbg         //  <   rtt_testbench
  , input  arct0_pseldbg                 //  <   rtt_testbench
  , input  arct0_penabledbg              //  <   rtt_testbench
  , input  arct0_pwritedbg               //  <   rtt_testbench
  , input  [31:0] arct0_pwdatadbg        //  <   rtt_testbench
  , input  arct0_dbgen                   //  <   rtt_testbench
  , input  arct0_niden                   //  <   rtt_testbench
  , input  swe_atready                   //  <   rtt_testbench
  , input  swe_afvalid                   //  <   rtt_testbench
  , input  swe_syncreq                   //  <   rtt_testbench
  , input  [32:0] sl0_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl0_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl0_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl1_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl1_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl1_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl2_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl2_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl2_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl3_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl3_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl3_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl4_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl4_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl4_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl5_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl5_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl5_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl6_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl6_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl6_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl7_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl7_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl7_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl8_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl8_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl8_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl9_alt_rtt_swe_data   //  <   rtt_testbench
  , input  sl9_alt_rtt_swe_val           //  <   rtt_testbench
  , input  [7:0] sl9_alt_rtt_swe_ext     //  <   rtt_testbench
  , input  [32:0] sl10_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl10_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl10_alt_rtt_swe_ext    //  <   rtt_testbench
  , input  [32:0] sl11_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl11_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl11_alt_rtt_swe_ext    //  <   rtt_testbench
  , input  [32:0] sl12_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl12_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl12_alt_rtt_swe_ext    //  <   rtt_testbench
  , input  [32:0] sl13_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl13_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl13_alt_rtt_swe_ext    //  <   rtt_testbench
  , input  [32:0] sl14_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl14_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl14_alt_rtt_swe_ext    //  <   rtt_testbench
  , input  [32:0] sl15_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl15_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl15_alt_rtt_swe_ext    //  <   rtt_testbench
  , input  [32:0] sl16_alt_rtt_swe_data  //  <   rtt_testbench
  , input  sl16_alt_rtt_swe_val          //  <   rtt_testbench
  , input  [7:0] sl16_alt_rtt_swe_ext    //  <   rtt_testbench
  , output [3:0] cbu_axi_arid            //    > alb_mss_fab
  , output cbu_axi_arvalid               //    > alb_mss_fab
  , output [39:0] cbu_axi_araddr         //    > alb_mss_fab
  , output [1:0] cbu_axi_arburst         //    > alb_mss_fab
  , output [2:0] cbu_axi_arsize          //    > alb_mss_fab
  , output [1:0] cbu_axi_arlock          //    > alb_mss_fab
  , output [3:0] cbu_axi_arlen           //    > alb_mss_fab
  , output [3:0] cbu_axi_arcache         //    > alb_mss_fab
  , output [2:0] cbu_axi_arprot          //    > alb_mss_fab
  , output cbu_axi_rready                //    > alb_mss_fab
  , output [3:0] cbu_axi_awid            //    > alb_mss_fab
  , output cbu_axi_awvalid               //    > alb_mss_fab
  , output [39:0] cbu_axi_awaddr         //    > alb_mss_fab
  , output [1:0] cbu_axi_awburst         //    > alb_mss_fab
  , output [2:0] cbu_axi_awsize          //    > alb_mss_fab
  , output [1:0] cbu_axi_awlock          //    > alb_mss_fab
  , output [3:0] cbu_axi_awlen           //    > alb_mss_fab
  , output [3:0] cbu_axi_awcache         //    > alb_mss_fab
  , output [2:0] cbu_axi_awprot          //    > alb_mss_fab
  , output [3:0] cbu_axi_wid             //    > alb_mss_fab
  , output cbu_axi_wvalid                //    > alb_mss_fab
  , output [63:0] cbu_axi_wdata          //    > alb_mss_fab
  , output [7:0] cbu_axi_wstrb           //    > alb_mss_fab
  , output cbu_axi_wlast                 //    > alb_mss_fab
  , output cbu_axi_bready                //    > alb_mss_fab
  , output sccm_axi_arready              //    > alb_mss_fab
  , output [15:0] sccm_axi_rid           //    > alb_mss_fab
  , output sccm_axi_rvalid               //    > alb_mss_fab
  , output [63:0] sccm_axi_rdata         //    > alb_mss_fab
  , output [1:0] sccm_axi_rresp          //    > alb_mss_fab
  , output sccm_axi_rlast                //    > alb_mss_fab
  , output sccm_axi_awready              //    > alb_mss_fab
  , output sccm_axi_wready               //    > alb_mss_fab
  , output [15:0] sccm_axi_bid           //    > alb_mss_fab
  , output sccm_axi_bvalid               //    > alb_mss_fab
  , output [1:0] sccm_axi_bresp          //    > alb_mss_fab
  , output dbg_rerr                      //    > fast_rascal
  , output debug_reset                   //    > alb_mss_ext_stub
  , output watchdog_reset                //    > alb_mss_ext_stub
  , output wdt_ext_timeout_r             //    > alb_mss_ext_stub
  , output wdt_reset                     //    > alb_mss_ext_stub
  , output wdt_reset_wdt_clk             //    > alb_mss_ext_stub
  , output sys_tf_halt_r                 //    > alb_mss_ext_stub
  , output fs_dc_tag_ecc_sb_error_r      //    > alb_mss_ext_stub
  , output fs_dc_tag_ecc_db_error_r      //    > alb_mss_ext_stub
  , output fs_dc_data_ecc_sb_error_r     //    > alb_mss_ext_stub
  , output fs_dc_data_ecc_db_error_r     //    > alb_mss_ext_stub
  , output fs_dccm_ecc_sb_error_r        //    > alb_mss_ext_stub
  , output fs_dccm_ecc_db_error_r        //    > alb_mss_ext_stub
  , output fs_itlb_ecc_sb_error_r        //    > alb_mss_ext_stub
  , output fs_itlb_ecc_db_error_r        //    > alb_mss_ext_stub
  , output fs_dtlb_ecc_sb_error_r        //    > alb_mss_ext_stub
  , output fs_dtlb_ecc_db_error_r        //    > alb_mss_ext_stub
  , output fs_ic_tag_ecc_sb_error_r      //    > alb_mss_ext_stub
  , output fs_ic_tag_ecc_db_error_r      //    > alb_mss_ext_stub
  , output fs_ic_data_ecc_sb_error_r     //    > alb_mss_ext_stub
  , output fs_ic_data_ecc_db_error_r     //    > alb_mss_ext_stub
  , output cc_idle                       //    > alb_mss_ext_stub
  , output [63:0] atdata                 //    > rtt_testbench
  , output [2:0] atbytes                 //    > rtt_testbench
  , output [6:0] atid                    //    > rtt_testbench
  , output atvalid                       //    > rtt_testbench
  , output afready                       //    > rtt_testbench
  , output [63:0] swe_atdata             //    > rtt_testbench
  , output [2:0] swe_atbytes             //    > rtt_testbench
  , output [6:0] swe_atid                //    > rtt_testbench
  , output swe_atvalid                   //    > rtt_testbench
  , output swe_afready                   //    > rtt_testbench
  , output arct0_preadydbg               //    > rtt_testbench
  , output [31:0] arct0_prdatadbg        //    > rtt_testbench
  , output arct0_pslverrdbg              //    > rtt_testbench
  , output sl0_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl1_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl2_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl3_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl4_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl5_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl6_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl7_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl8_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl9_alt_rtt_swe_prdcr_en      //    > rtt_testbench
  , output sl10_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output sl11_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output sl12_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output sl13_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output sl14_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output sl15_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output sl16_alt_rtt_swe_prdcr_en     //    > rtt_testbench
  , output dbg_cmdack                    //    > fast_rascal
  , output dbg_rspval                    //    > fast_rascal
  , output [31:0] dbg_rdata              //    > fast_rascal
  , output dbg_reop                      //    > fast_rascal
  , output sys_halt_r                    //    > fast_rascal
  , output preadydbg                     //    > fast_rascal
  , output [31:0] prdatadbg              //    > fast_rascal
  , output pslverrdbg                    //    > fast_rascal
  , output [25:0] cti_rtt_filters        //    > rtt_cti_stub
  , output cti_halt                      //    > rtt_cti_stub
  , output cti_break                     //    > rtt_cti_stub
  , output cti_sleep                     //    > rtt_cti_stub
  , output cti_ap_hit                    //    > rtt_cti_stub
  , output [7:0] cti_ap_status           //    > rtt_cti_stub
  , output arc_halt_ack                  //    > io_pad_ring
  , output arc_run_ack                   //    > io_pad_ring
  , output sys_sleep_r                   //    > io_pad_ring
  , output [2:0] sys_sleep_mode_r        //    > io_pad_ring
  , output EventManager_evm_wakeup       //    > apex_testbench
  , output [63:0] EventManager_evm_send  //    > apex_testbench
  , output [31:0] EventManager_vm_grp0_sid //    > apex_testbench
  , output [31:0] EventManager_vm_grp0_ssid //    > apex_testbench
  , output [31:0] EventManager_vm_grp1_sid //    > apex_testbench
  , output [31:0] EventManager_vm_grp1_ssid //    > apex_testbench
  , output [31:0] EventManager_vm_grp2_sid //    > apex_testbench
  , output [31:0] EventManager_vm_grp3_sid //    > apex_testbench
  , output [31:0] EventManager_vm_grp2_ssid //    > apex_testbench
  , output [31:0] EventManager_vm_grp3_ssid //    > apex_testbench
  , output EventManager_evt_vm_irq       //    > apex_testbench
  , output [3:0] EventManager_evt_vm_sel //    > apex_testbench
  );

// Intermediate signals:
wire   [`npuarc_AUX_DATA-1:0] i_rtt_drd_r;      // rtt > hs_cluster_top -- rtt.rtt_drd_r [31:0]
wire   i_rtt_prod_sel;                   // rtt > hs_cluster_top -- rtt.rtt_prod_sel
wire   i_rtt_freeze;                     // rtt > hs_cluster_top -- rtt.rtt_freeze
wire   [7:0] i_rtt_src_num;              // rtt > hs_cluster_top -- rtt.rtt_src_num [7:0]
wire   i_rtt_write_a;                    // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_write_a
wire   i_rtt_read_a;                     // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_read_a
wire   [31:0] i_rtt_addr_r;              // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_addr_r [31:0]
wire   [31:0] i_rtt_dwr_r;               // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_dwr_r [31:0]
wire   i_rtt_ss_halt;                    // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_ss_halt
wire   i_rtt_hw_bp;                      // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_hw_bp
wire   i_rtt_hw_exc;                     // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_hw_exc
wire   i_rtt_dbg_halt;                   // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_dbg_halt
wire   i_rtt_rst_applied;                // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_rst_applied
wire   i_rtt_uop_is_leave;               // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_uop_is_leave
wire   i_rtt_in_deslot;                  // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_in_deslot
wire   i_rtt_in_eslot;                   // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_in_eslot
wire   i_rtt_inst_commit;                // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_inst_commit
wire   [31:1] i_rtt_inst_addr;           // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_inst_addr [31:1]
wire   i_rtt_cond_valid;                 // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_cond_valid
wire   i_rtt_cond_pass;                  // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_cond_pass
wire   i_rtt_branch;                     // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_branch
wire   i_rtt_branch_indir;               // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_branch_indir
wire   [31:1] i_rtt_branch_taddr;        // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_branch_taddr [31:1]
wire   i_rtt_dslot;                      // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_dslot
wire   i_rtt_exception;                  // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_exception
wire   i_rtt_exception_rtn;              // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_exception_rtn
wire   i_rtt_interrupt;                  // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_interrupt
wire   i_rtt_sleep_mode;                 // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_sleep_mode
wire   i_rtt_zd_loop;                    // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_zd_loop
wire   [7:0] i_rtt_wp_val;               // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_wp_val [7:0]
wire   i_rtt_wp_hit;                     // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_wp_hit
wire   i_rtt_sw_bp;                      // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_sw_bp
wire   i_sys_halt_r;                     // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.sys_halt_r
wire   [7:0] i_rtt_process_id;           // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_process_id [7:0]
wire   i_rtt_pid_wr_en;                  // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_pid_wr_en
wire   [32:0] i_rtt_swe_data;            // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_swe_data [32:0]
wire   i_rtt_swe_val;                    // hs_cluster_top > rtt -- hs_cluster_top.alb_cpu_top.rtt_swe_val

// Instantiation of module hs_cluster_top
npuarc_hs_cluster_top ihs_cluster_top(
    .cbu_axi_rid               (cbu_axi_rid)       // <   alb_mss_fab
  , .cbu_axi_arready           (cbu_axi_arready)   // <   alb_mss_fab
  , .cbu_axi_rvalid            (cbu_axi_rvalid)    // <   alb_mss_fab
  , .cbu_axi_rdata             (cbu_axi_rdata)     // <   alb_mss_fab
  , .cbu_axi_rresp             (cbu_axi_rresp)     // <   alb_mss_fab
  , .cbu_axi_rlast             (cbu_axi_rlast)     // <   alb_mss_fab
  , .cbu_axi_bid               (cbu_axi_bid)       // <   alb_mss_fab
  , .cbu_axi_awready           (cbu_axi_awready)   // <   alb_mss_fab
  , .cbu_axi_wready            (cbu_axi_wready)    // <   alb_mss_fab
  , .cbu_axi_bvalid            (cbu_axi_bvalid)    // <   alb_mss_fab
  , .cbu_axi_bresp             (cbu_axi_bresp)     // <   alb_mss_fab
  , .sccm_axi_arvalid          (sccm_axi_arvalid)  // <   alb_mss_fab
  , .sccm_axi_arid             (sccm_axi_arid)     // <   alb_mss_fab
  , .sccm_axi_araddr           (sccm_axi_araddr)   // <   alb_mss_fab
  , .sccm_axi_arregion         (sccm_axi_arregion) // <   alb_mss_fab
  , .sccm_axi_arburst          (sccm_axi_arburst)  // <   alb_mss_fab
  , .sccm_axi_arlen            (sccm_axi_arlen)    // <   alb_mss_fab
  , .sccm_axi_arsize           (sccm_axi_arsize)   // <   alb_mss_fab
  , .sccm_axi_rready           (sccm_axi_rready)   // <   alb_mss_fab
  , .sccm_axi_awvalid          (sccm_axi_awvalid)  // <   alb_mss_fab
  , .sccm_axi_awid             (sccm_axi_awid)     // <   alb_mss_fab
  , .sccm_axi_awaddr           (sccm_axi_awaddr)   // <   alb_mss_fab
  , .sccm_axi_awregion         (sccm_axi_awregion) // <   alb_mss_fab
  , .sccm_axi_awburst          (sccm_axi_awburst)  // <   alb_mss_fab
  , .sccm_axi_awlen            (sccm_axi_awlen)    // <   alb_mss_fab
  , .sccm_axi_awsize           (sccm_axi_awsize)   // <   alb_mss_fab
  , .sccm_axi_wvalid           (sccm_axi_wvalid)   // <   alb_mss_fab
  , .sccm_axi_wdata            (sccm_axi_wdata)    // <   alb_mss_fab
  , .sccm_axi_wstrb            (sccm_axi_wstrb)    // <   alb_mss_fab
  , .sccm_axi_wlast            (sccm_axi_wlast)    // <   alb_mss_fab
  , .sccm_axi_bready           (sccm_axi_bready)   // <   alb_mss_fab
  , .mbus_clk_en               (mbus_clk_en)       // <   alb_mss_clkctrl
  , .dbus_clk_en               (dbus_clk_en)       // <   alb_mss_clkctrl
  , .clk                       (clk)               // <   alb_mss_clkctrl
  , .rst_a                     (rst_a)             // <   io_pad_ring
  , .clusternum                (clusternum)        // <   io_pad_ring
  , .test_mode                 (test_mode)         // <   io_pad_ring
  , .arc_event_a               (arc_event_a)       // <   io_pad_ring
  , .arc_halt_req_a            (arc_halt_req_a)    // <   io_pad_ring
  , .arc_run_req_a             (arc_run_req_a)     // <   io_pad_ring
  , .EventManager_evm_event_a  (EventManager_evm_event_a) // <   apex_testbench.EventManager_tb
  , .EventManager_evm_sleep    (EventManager_evm_sleep) // <   apex_testbench.EventManager_tb
  , .irq17_a                   (irq17_a)           // <   alb_mss_ext_stub
  , .irq19_a                   (irq19_a)           // <   alb_mss_ext_stub
  , .irq21_a                   (irq21_a)           // <   alb_mss_ext_stub
  , .irq22_a                   (irq22_a)           // <   alb_mss_ext_stub
  , .irq23_a                   (irq23_a)           // <   alb_mss_ext_stub
  , .irq24_a                   (irq24_a)           // <   alb_mss_ext_stub
  , .irq25_a                   (irq25_a)           // <   alb_mss_ext_stub
  , .irq26_a                   (irq26_a)           // <   alb_mss_ext_stub
  , .irq27_a                   (irq27_a)           // <   alb_mss_ext_stub
  , .irq28_a                   (irq28_a)           // <   alb_mss_ext_stub
  , .irq29_a                   (irq29_a)           // <   alb_mss_ext_stub
  , .irq30_a                   (irq30_a)           // <   alb_mss_ext_stub
  , .irq31_a                   (irq31_a)           // <   alb_mss_ext_stub
  , .irq32_a                   (irq32_a)           // <   alb_mss_ext_stub
  , .irq33_a                   (irq33_a)           // <   alb_mss_ext_stub
  , .irq34_a                   (irq34_a)           // <   alb_mss_ext_stub
  , .irq35_a                   (irq35_a)           // <   alb_mss_ext_stub
  , .irq36_a                   (irq36_a)           // <   alb_mss_ext_stub
  , .irq37_a                   (irq37_a)           // <   alb_mss_ext_stub
  , .irq38_a                   (irq38_a)           // <   alb_mss_ext_stub
  , .irq39_a                   (irq39_a)           // <   alb_mss_ext_stub
  , .irq40_a                   (irq40_a)           // <   alb_mss_ext_stub
  , .irq41_a                   (irq41_a)           // <   alb_mss_ext_stub
  , .irq42_a                   (irq42_a)           // <   alb_mss_ext_stub
  , .irq43_a                   (irq43_a)           // <   alb_mss_ext_stub
  , .irq44_a                   (irq44_a)           // <   alb_mss_ext_stub
  , .irq45_a                   (irq45_a)           // <   alb_mss_ext_stub
  , .irq46_a                   (irq46_a)           // <   alb_mss_ext_stub
  , .irq47_a                   (irq47_a)           // <   alb_mss_ext_stub
  , .irq48_a                   (irq48_a)           // <   alb_mss_ext_stub
  , .irq49_a                   (irq49_a)           // <   alb_mss_ext_stub
  , .irq50_a                   (irq50_a)           // <   alb_mss_ext_stub
  , .irq51_a                   (irq51_a)           // <   alb_mss_ext_stub
  , .irq52_a                   (irq52_a)           // <   alb_mss_ext_stub
  , .irq53_a                   (irq53_a)           // <   alb_mss_ext_stub
  , .irq54_a                   (irq54_a)           // <   alb_mss_ext_stub
  , .intvbase_in               (intvbase_in)       // <   io_pad_ring
  , .dbg_cmdval                (dbg_cmdval)        // <   fast_rascal
  , .dbg_eop                   (dbg_eop)           // <   fast_rascal
  , .dbg_address               (dbg_address)       // <   fast_rascal
  , .dbg_be                    (dbg_be)            // <   fast_rascal
  , .dbg_cmd                   (dbg_cmd)           // <   fast_rascal
  , .dbg_wdata                 (dbg_wdata)         // <   fast_rascal
  , .dbg_rspack                (dbg_rspack)        // <   fast_rascal
  , .dbg_prot_sel              (dbg_prot_sel)      // <   fast_rascal
  , .pclkdbg_en                (pclkdbg_en)        // <   clock_and_reset
  , .presetdbgn                (presetdbgn)        // <   clock_and_reset
  , .paddrdbg                  (paddrdbg)          // <   fast_rascal
  , .pseldbg                   (pseldbg)           // <   fast_rascal
  , .penabledbg                (penabledbg)        // <   fast_rascal
  , .pwritedbg                 (pwritedbg)         // <   fast_rascal
  , .pwdatadbg                 (pwdatadbg)         // <   fast_rascal
  , .dbgen                     (dbgen)             // <   fast_rascal
  , .niden                     (niden)             // <   fast_rascal
  , .dbg_cache_rst_disable     (dbg_cache_rst_disable) // <   alb_mss_ext_stub
  , .dccm_dmi_priority         (dccm_dmi_priority) // <   alb_mss_ext_stub
  , .rtt_drd_r                 (i_rtt_drd_r)       // <   rtt
  , .rtt_prod_sel              (i_rtt_prod_sel)    // <   rtt
  , .rtt_freeze                (i_rtt_freeze)      // <   rtt
  , .rtt_src_num               (i_rtt_src_num)     // <   rtt
  , .arcnum                    (arcnum)            // <   io_pad_ring
  , .wdt_clk                   (wdt_clk)           // <   alb_mss_clkctrl
  , .wdt_ext_timeout_ack_r     (wdt_ext_timeout_ack_r) // <   alb_mss_ext_stub
  , .mem_ds                    (mem_ds)            // <   alb_mss_ext_stub
  , .mem_sd                    (mem_sd)            // <   alb_mss_ext_stub
  , .rtt_write_a               (i_rtt_write_a)     //   > rtt
  , .rtt_read_a                (i_rtt_read_a)      //   > rtt
  , .rtt_addr_r                (i_rtt_addr_r)      //   > rtt
  , .rtt_dwr_r                 (i_rtt_dwr_r)       //   > rtt
  , .rtt_ss_halt               (i_rtt_ss_halt)     //   > rtt
  , .rtt_hw_bp                 (i_rtt_hw_bp)       //   > rtt
  , .rtt_hw_exc                (i_rtt_hw_exc)      //   > rtt
  , .rtt_dbg_halt              (i_rtt_dbg_halt)    //   > rtt
  , .rtt_rst_applied           (i_rtt_rst_applied) //   > rtt
  , .rtt_uop_is_leave          (i_rtt_uop_is_leave) //   > rtt
  , .rtt_in_deslot             (i_rtt_in_deslot)   //   > rtt
  , .rtt_in_eslot              (i_rtt_in_eslot)    //   > rtt
  , .rtt_inst_commit           (i_rtt_inst_commit) //   > rtt
  , .rtt_inst_addr             (i_rtt_inst_addr)   //   > rtt
  , .rtt_cond_valid            (i_rtt_cond_valid)  //   > rtt
  , .rtt_cond_pass             (i_rtt_cond_pass)   //   > rtt
  , .rtt_branch                (i_rtt_branch)      //   > rtt
  , .rtt_branch_indir          (i_rtt_branch_indir) //   > rtt
  , .rtt_branch_taddr          (i_rtt_branch_taddr) //   > rtt
  , .rtt_dslot                 (i_rtt_dslot)       //   > rtt
  , .rtt_exception             (i_rtt_exception)   //   > rtt
  , .rtt_exception_rtn         (i_rtt_exception_rtn) //   > rtt
  , .rtt_interrupt             (i_rtt_interrupt)   //   > rtt
  , .rtt_sleep_mode            (i_rtt_sleep_mode)  //   > rtt
  , .rtt_zd_loop               (i_rtt_zd_loop)     //   > rtt
  , .rtt_wp_val                (i_rtt_wp_val)      //   > rtt
  , .rtt_wp_hit                (i_rtt_wp_hit)      //   > rtt
  , .rtt_sw_bp                 (i_rtt_sw_bp)       //   > rtt
  , .sys_halt_r                (i_sys_halt_r)      //   > rtt
  , .rtt_process_id            (i_rtt_process_id)  //   > rtt
  , .rtt_pid_wr_en             (i_rtt_pid_wr_en)   //   > rtt
  , .rtt_swe_data              (i_rtt_swe_data)    //   > rtt
  , .rtt_swe_val               (i_rtt_swe_val)     //   > rtt
  , .cbu_axi_arid              (cbu_axi_arid)      //   > alb_mss_fab
  , .cbu_axi_arvalid           (cbu_axi_arvalid)   //   > alb_mss_fab
  , .cbu_axi_araddr            (cbu_axi_araddr)    //   > alb_mss_fab
  , .cbu_axi_arburst           (cbu_axi_arburst)   //   > alb_mss_fab
  , .cbu_axi_arsize            (cbu_axi_arsize)    //   > alb_mss_fab
  , .cbu_axi_arlock            (cbu_axi_arlock)    //   > alb_mss_fab
  , .cbu_axi_arlen             (cbu_axi_arlen)     //   > alb_mss_fab
  , .cbu_axi_arcache           (cbu_axi_arcache)   //   > alb_mss_fab
  , .cbu_axi_arprot            (cbu_axi_arprot)    //   > alb_mss_fab
  , .cbu_axi_rready            (cbu_axi_rready)    //   > alb_mss_fab
  , .cbu_axi_awid              (cbu_axi_awid)      //   > alb_mss_fab
  , .cbu_axi_awvalid           (cbu_axi_awvalid)   //   > alb_mss_fab
  , .cbu_axi_awaddr            (cbu_axi_awaddr)    //   > alb_mss_fab
  , .cbu_axi_awburst           (cbu_axi_awburst)   //   > alb_mss_fab
  , .cbu_axi_awsize            (cbu_axi_awsize)    //   > alb_mss_fab
  , .cbu_axi_awlock            (cbu_axi_awlock)    //   > alb_mss_fab
  , .cbu_axi_awlen             (cbu_axi_awlen)     //   > alb_mss_fab
  , .cbu_axi_awcache           (cbu_axi_awcache)   //   > alb_mss_fab
  , .cbu_axi_awprot            (cbu_axi_awprot)    //   > alb_mss_fab
  , .cbu_axi_wid               (cbu_axi_wid)       //   > alb_mss_fab
  , .cbu_axi_wvalid            (cbu_axi_wvalid)    //   > alb_mss_fab
  , .cbu_axi_wdata             (cbu_axi_wdata)     //   > alb_mss_fab
  , .cbu_axi_wstrb             (cbu_axi_wstrb)     //   > alb_mss_fab
  , .cbu_axi_wlast             (cbu_axi_wlast)     //   > alb_mss_fab
  , .cbu_axi_bready            (cbu_axi_bready)    //   > alb_mss_fab
  , .sccm_axi_arready          (sccm_axi_arready)  //   > alb_mss_fab
  , .sccm_axi_rid              (sccm_axi_rid)      //   > alb_mss_fab
  , .sccm_axi_rvalid           (sccm_axi_rvalid)   //   > alb_mss_fab
  , .sccm_axi_rdata            (sccm_axi_rdata)    //   > alb_mss_fab
  , .sccm_axi_rresp            (sccm_axi_rresp)    //   > alb_mss_fab
  , .sccm_axi_rlast            (sccm_axi_rlast)    //   > alb_mss_fab
  , .sccm_axi_awready          (sccm_axi_awready)  //   > alb_mss_fab
  , .sccm_axi_wready           (sccm_axi_wready)   //   > alb_mss_fab
  , .sccm_axi_bid              (sccm_axi_bid)      //   > alb_mss_fab
  , .sccm_axi_bvalid           (sccm_axi_bvalid)   //   > alb_mss_fab
  , .sccm_axi_bresp            (sccm_axi_bresp)    //   > alb_mss_fab
  , .dbg_rerr                  (dbg_rerr)          //   > alb_mss_ext_stub
  , .debug_reset               (debug_reset)       //   > alb_mss_ext_stub
  , .watchdog_reset            (watchdog_reset)    //   > alb_mss_ext_stub
  , .wdt_ext_timeout_r         (wdt_ext_timeout_r) //   > alb_mss_ext_stub
  , .wdt_reset                 (wdt_reset)         //   > alb_mss_ext_stub
  , .wdt_reset_wdt_clk         (wdt_reset_wdt_clk) //   > alb_mss_ext_stub
  , .sys_tf_halt_r             (sys_tf_halt_r)     //   > alb_mss_ext_stub
  , .fs_dc_tag_ecc_sb_error_r  (fs_dc_tag_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_dc_tag_ecc_db_error_r  (fs_dc_tag_ecc_db_error_r) //   > alb_mss_ext_stub
  , .fs_dc_data_ecc_sb_error_r (fs_dc_data_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_dc_data_ecc_db_error_r (fs_dc_data_ecc_db_error_r) //   > alb_mss_ext_stub
  , .fs_dccm_ecc_sb_error_r    (fs_dccm_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_dccm_ecc_db_error_r    (fs_dccm_ecc_db_error_r) //   > alb_mss_ext_stub
  , .fs_itlb_ecc_sb_error_r    (fs_itlb_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_itlb_ecc_db_error_r    (fs_itlb_ecc_db_error_r) //   > alb_mss_ext_stub
  , .fs_dtlb_ecc_sb_error_r    (fs_dtlb_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_dtlb_ecc_db_error_r    (fs_dtlb_ecc_db_error_r) //   > alb_mss_ext_stub
  , .fs_ic_tag_ecc_sb_error_r  (fs_ic_tag_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_ic_tag_ecc_db_error_r  (fs_ic_tag_ecc_db_error_r) //   > alb_mss_ext_stub
  , .fs_ic_data_ecc_sb_error_r (fs_ic_data_ecc_sb_error_r) //   > alb_mss_ext_stub
  , .fs_ic_data_ecc_db_error_r (fs_ic_data_ecc_db_error_r) //   > alb_mss_ext_stub
  , .cc_idle                   (cc_idle)           //   > alb_mss_ext_stub
  , .dbg_cmdack                (dbg_cmdack)        //   > fast_rascal
  , .dbg_rspval                (dbg_rspval)        //   > fast_rascal
  , .dbg_rdata                 (dbg_rdata)         //   > fast_rascal
  , .dbg_reop                  (dbg_reop)          //   > fast_rascal
  , .preadydbg                 (preadydbg)         //   > fast_rascal
  , .prdatadbg                 (prdatadbg)         //   > fast_rascal
  , .pslverrdbg                (pslverrdbg)        //   > fast_rascal
  , .cti_halt                  (cti_halt)          //   > rtt_cti_stub
  , .cti_break                 (cti_break)         //   > rtt_cti_stub
  , .cti_sleep                 (cti_sleep)         //   > rtt_cti_stub
  , .cti_ap_hit                (cti_ap_hit)        //   > rtt_cti_stub
  , .cti_ap_status             (cti_ap_status)     //   > rtt_cti_stub
  , .arc_halt_ack              (arc_halt_ack)      //   > io_pad_ring
  , .arc_run_ack               (arc_run_ack)       //   > io_pad_ring
  , .sys_sleep_r               (sys_sleep_r)       //   > io_pad_ring
  , .sys_sleep_mode_r          (sys_sleep_mode_r)  //   > io_pad_ring
  , .EventManager_evm_wakeup   (EventManager_evm_wakeup) //   > apex_testbench
  , .EventManager_evm_send     (EventManager_evm_send) //   > apex_testbench
  , .EventManager_vm_grp0_sid  (EventManager_vm_grp0_sid) //   > apex_testbench
  , .EventManager_vm_grp0_ssid (EventManager_vm_grp0_ssid) //   > apex_testbench
  , .EventManager_vm_grp1_sid  (EventManager_vm_grp1_sid) //   > apex_testbench
  , .EventManager_vm_grp1_ssid (EventManager_vm_grp1_ssid) //   > apex_testbench
  , .EventManager_vm_grp2_sid  (EventManager_vm_grp2_sid) //   > apex_testbench
  , .EventManager_vm_grp3_sid  (EventManager_vm_grp3_sid) //   > apex_testbench
  , .EventManager_vm_grp2_ssid (EventManager_vm_grp2_ssid) //   > apex_testbench
  , .EventManager_vm_grp3_ssid (EventManager_vm_grp3_ssid) //   > apex_testbench
  , .EventManager_evt_vm_irq   (EventManager_evt_vm_irq) //   > apex_testbench
  , .EventManager_evt_vm_sel   (EventManager_evt_vm_sel) //   > apex_testbench
  );

// Instantiation of module rtt
npuarc_rtt irtt(
    .rtt_clk                   (rtt_clk)           // <   alb_mss_clkctrl
  , .atclken                   (atclken)           // <   rtt_testbench
  , .atresetn                  (atresetn)          // <   rtt_testbench
  , .atb_cstimestamp           (atb_cstimestamp)   // <   rtt_csts_gen
  , .rtt_write_a               (i_rtt_write_a)     // <   hs_cluster_top.alb_cpu_top
  , .rtt_read_a                (i_rtt_read_a)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_addr_r                (i_rtt_addr_r)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_dwr_r                 (i_rtt_dwr_r)       // <   hs_cluster_top.alb_cpu_top
  , .rtt_ss_halt               (i_rtt_ss_halt)     // <   hs_cluster_top.alb_cpu_top
  , .rtt_hw_bp                 (i_rtt_hw_bp)       // <   hs_cluster_top.alb_cpu_top
  , .rtt_hw_exc                (i_rtt_hw_exc)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_dbg_halt              (i_rtt_dbg_halt)    // <   hs_cluster_top.alb_cpu_top
  , .rtt_rst_applied           (i_rtt_rst_applied) // <   hs_cluster_top.alb_cpu_top
  , .rtt_uop_is_leave          (i_rtt_uop_is_leave) // <   hs_cluster_top.alb_cpu_top
  , .rtt_in_deslot             (i_rtt_in_deslot)   // <   hs_cluster_top.alb_cpu_top
  , .rtt_in_eslot              (i_rtt_in_eslot)    // <   hs_cluster_top.alb_cpu_top
  , .rtt_inst_commit           (i_rtt_inst_commit) // <   hs_cluster_top.alb_cpu_top
  , .rtt_inst_addr             (i_rtt_inst_addr)   // <   hs_cluster_top.alb_cpu_top
  , .rtt_cond_valid            (i_rtt_cond_valid)  // <   hs_cluster_top.alb_cpu_top
  , .rtt_cond_pass             (i_rtt_cond_pass)   // <   hs_cluster_top.alb_cpu_top
  , .rtt_branch                (i_rtt_branch)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_branch_indir          (i_rtt_branch_indir) // <   hs_cluster_top.alb_cpu_top
  , .rtt_branch_taddr          (i_rtt_branch_taddr) // <   hs_cluster_top.alb_cpu_top
  , .rtt_dslot                 (i_rtt_dslot)       // <   hs_cluster_top.alb_cpu_top
  , .rtt_exception             (i_rtt_exception)   // <   hs_cluster_top.alb_cpu_top
  , .rtt_exception_rtn         (i_rtt_exception_rtn) // <   hs_cluster_top.alb_cpu_top
  , .rtt_interrupt             (i_rtt_interrupt)   // <   hs_cluster_top.alb_cpu_top
  , .rtt_sleep_mode            (i_rtt_sleep_mode)  // <   hs_cluster_top.alb_cpu_top
  , .rtt_zd_loop               (i_rtt_zd_loop)     // <   hs_cluster_top.alb_cpu_top
  , .rtt_wp_val                (i_rtt_wp_val)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_wp_hit                (i_rtt_wp_hit)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_sw_bp                 (i_rtt_sw_bp)       // <   hs_cluster_top.alb_cpu_top
  , .sys_halt_r                (i_sys_halt_r)      // <   hs_cluster_top.alb_cpu_top
  , .rtt_process_id            (i_rtt_process_id)  // <   hs_cluster_top.alb_cpu_top
  , .rtt_pid_wr_en             (i_rtt_pid_wr_en)   // <   hs_cluster_top.alb_cpu_top
  , .rtt_swe_data              (i_rtt_swe_data)    // <   hs_cluster_top.alb_cpu_top
  , .rtt_swe_val               (i_rtt_swe_val)     // <   hs_cluster_top.alb_cpu_top
  , .atready                   (atready)           // <   rtt_testbench
  , .afvalid                   (afvalid)           // <   rtt_testbench
  , .syncreq                   (syncreq)           // <   rtt_testbench
  , .cti_trace_start           (cti_trace_start)   // <   rtt_cti_stub
  , .cti_trace_stop            (cti_trace_stop)    // <   rtt_cti_stub
  , .pclkdbg_en                (pclkdbg_en)        // <   clock_and_reset
  , .presetdbgn                (presetdbgn)        // <   clock_and_reset
  , .arct0_paddrdbg            (arct0_paddrdbg)    // <   rtt_testbench
  , .arct0_pseldbg             (arct0_pseldbg)     // <   rtt_testbench
  , .arct0_penabledbg          (arct0_penabledbg)  // <   rtt_testbench
  , .arct0_pwritedbg           (arct0_pwritedbg)   // <   rtt_testbench
  , .arct0_pwdatadbg           (arct0_pwdatadbg)   // <   rtt_testbench
  , .arct0_dbgen               (arct0_dbgen)       // <   rtt_testbench
  , .arct0_niden               (arct0_niden)       // <   rtt_testbench
  , .swe_atready               (swe_atready)       // <   rtt_testbench
  , .swe_afvalid               (swe_afvalid)       // <   rtt_testbench
  , .swe_syncreq               (swe_syncreq)       // <   rtt_testbench
  , .sl0_alt_rtt_swe_data      (sl0_alt_rtt_swe_data) // <   rtt_testbench
  , .sl0_alt_rtt_swe_val       (sl0_alt_rtt_swe_val) // <   rtt_testbench
  , .sl0_alt_rtt_swe_ext       (sl0_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl1_alt_rtt_swe_data      (sl1_alt_rtt_swe_data) // <   rtt_testbench
  , .sl1_alt_rtt_swe_val       (sl1_alt_rtt_swe_val) // <   rtt_testbench
  , .sl1_alt_rtt_swe_ext       (sl1_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl2_alt_rtt_swe_data      (sl2_alt_rtt_swe_data) // <   rtt_testbench
  , .sl2_alt_rtt_swe_val       (sl2_alt_rtt_swe_val) // <   rtt_testbench
  , .sl2_alt_rtt_swe_ext       (sl2_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl3_alt_rtt_swe_data      (sl3_alt_rtt_swe_data) // <   rtt_testbench
  , .sl3_alt_rtt_swe_val       (sl3_alt_rtt_swe_val) // <   rtt_testbench
  , .sl3_alt_rtt_swe_ext       (sl3_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl4_alt_rtt_swe_data      (sl4_alt_rtt_swe_data) // <   rtt_testbench
  , .sl4_alt_rtt_swe_val       (sl4_alt_rtt_swe_val) // <   rtt_testbench
  , .sl4_alt_rtt_swe_ext       (sl4_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl5_alt_rtt_swe_data      (sl5_alt_rtt_swe_data) // <   rtt_testbench
  , .sl5_alt_rtt_swe_val       (sl5_alt_rtt_swe_val) // <   rtt_testbench
  , .sl5_alt_rtt_swe_ext       (sl5_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl6_alt_rtt_swe_data      (sl6_alt_rtt_swe_data) // <   rtt_testbench
  , .sl6_alt_rtt_swe_val       (sl6_alt_rtt_swe_val) // <   rtt_testbench
  , .sl6_alt_rtt_swe_ext       (sl6_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl7_alt_rtt_swe_data      (sl7_alt_rtt_swe_data) // <   rtt_testbench
  , .sl7_alt_rtt_swe_val       (sl7_alt_rtt_swe_val) // <   rtt_testbench
  , .sl7_alt_rtt_swe_ext       (sl7_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl8_alt_rtt_swe_data      (sl8_alt_rtt_swe_data) // <   rtt_testbench
  , .sl8_alt_rtt_swe_val       (sl8_alt_rtt_swe_val) // <   rtt_testbench
  , .sl8_alt_rtt_swe_ext       (sl8_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl9_alt_rtt_swe_data      (sl9_alt_rtt_swe_data) // <   rtt_testbench
  , .sl9_alt_rtt_swe_val       (sl9_alt_rtt_swe_val) // <   rtt_testbench
  , .sl9_alt_rtt_swe_ext       (sl9_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl10_alt_rtt_swe_data     (sl10_alt_rtt_swe_data) // <   rtt_testbench
  , .sl10_alt_rtt_swe_val      (sl10_alt_rtt_swe_val) // <   rtt_testbench
  , .sl10_alt_rtt_swe_ext      (sl10_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl11_alt_rtt_swe_data     (sl11_alt_rtt_swe_data) // <   rtt_testbench
  , .sl11_alt_rtt_swe_val      (sl11_alt_rtt_swe_val) // <   rtt_testbench
  , .sl11_alt_rtt_swe_ext      (sl11_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl12_alt_rtt_swe_data     (sl12_alt_rtt_swe_data) // <   rtt_testbench
  , .sl12_alt_rtt_swe_val      (sl12_alt_rtt_swe_val) // <   rtt_testbench
  , .sl12_alt_rtt_swe_ext      (sl12_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl13_alt_rtt_swe_data     (sl13_alt_rtt_swe_data) // <   rtt_testbench
  , .sl13_alt_rtt_swe_val      (sl13_alt_rtt_swe_val) // <   rtt_testbench
  , .sl13_alt_rtt_swe_ext      (sl13_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl14_alt_rtt_swe_data     (sl14_alt_rtt_swe_data) // <   rtt_testbench
  , .sl14_alt_rtt_swe_val      (sl14_alt_rtt_swe_val) // <   rtt_testbench
  , .sl14_alt_rtt_swe_ext      (sl14_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl15_alt_rtt_swe_data     (sl15_alt_rtt_swe_data) // <   rtt_testbench
  , .sl15_alt_rtt_swe_val      (sl15_alt_rtt_swe_val) // <   rtt_testbench
  , .sl15_alt_rtt_swe_ext      (sl15_alt_rtt_swe_ext) // <   rtt_testbench
  , .sl16_alt_rtt_swe_data     (sl16_alt_rtt_swe_data) // <   rtt_testbench
  , .sl16_alt_rtt_swe_val      (sl16_alt_rtt_swe_val) // <   rtt_testbench
  , .sl16_alt_rtt_swe_ext      (sl16_alt_rtt_swe_ext) // <   rtt_testbench
  , .test_mode                 (test_mode)         // <   io_pad_ring
  , .rst_a                     (rst_a)             // <   io_pad_ring
  , .rtt_drd_r                 (i_rtt_drd_r)       //   > hs_cluster_top
  , .rtt_prod_sel              (i_rtt_prod_sel)    //   > hs_cluster_top
  , .rtt_freeze                (i_rtt_freeze)      //   > hs_cluster_top
  , .rtt_src_num               (i_rtt_src_num)     //   > hs_cluster_top
  , .atdata                    (atdata)            //   > rtt_testbench
  , .atbytes                   (atbytes)           //   > rtt_testbench
  , .atid                      (atid)              //   > rtt_testbench
  , .atvalid                   (atvalid)           //   > rtt_testbench
  , .afready                   (afready)           //   > rtt_testbench
  , .swe_atdata                (swe_atdata)        //   > rtt_testbench
  , .swe_atbytes               (swe_atbytes)       //   > rtt_testbench
  , .swe_atid                  (swe_atid)          //   > rtt_testbench
  , .swe_atvalid               (swe_atvalid)       //   > rtt_testbench
  , .swe_afready               (swe_afready)       //   > rtt_testbench
  , .arct0_preadydbg           (arct0_preadydbg)   //   > rtt_testbench
  , .arct0_prdatadbg           (arct0_prdatadbg)   //   > rtt_testbench
  , .arct0_pslverrdbg          (arct0_pslverrdbg)  //   > rtt_testbench
  , .sl0_alt_rtt_swe_prdcr_en  (sl0_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl1_alt_rtt_swe_prdcr_en  (sl1_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl2_alt_rtt_swe_prdcr_en  (sl2_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl3_alt_rtt_swe_prdcr_en  (sl3_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl4_alt_rtt_swe_prdcr_en  (sl4_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl5_alt_rtt_swe_prdcr_en  (sl5_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl6_alt_rtt_swe_prdcr_en  (sl6_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl7_alt_rtt_swe_prdcr_en  (sl7_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl8_alt_rtt_swe_prdcr_en  (sl8_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl9_alt_rtt_swe_prdcr_en  (sl9_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl10_alt_rtt_swe_prdcr_en (sl10_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl11_alt_rtt_swe_prdcr_en (sl11_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl12_alt_rtt_swe_prdcr_en (sl12_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl13_alt_rtt_swe_prdcr_en (sl13_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl14_alt_rtt_swe_prdcr_en (sl14_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl15_alt_rtt_swe_prdcr_en (sl15_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .sl16_alt_rtt_swe_prdcr_en (sl16_alt_rtt_swe_prdcr_en) //   > rtt_testbench
  , .cti_rtt_filters           (cti_rtt_filters)   //   > rtt_cti_stub
  );

// Output drives
assign sys_halt_r = i_sys_halt_r;
endmodule
