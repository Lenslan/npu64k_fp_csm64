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

module npuarc_hs_cluster_top(
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
  , input  rst_a                         //  <   io_pad_ring
  , input  [7:0] clusternum              //  <   io_pad_ring
  , input  test_mode                     //  <   io_pad_ring
  , input  arc_event_a                   //  <   io_pad_ring
  , input  arc_halt_req_a                //  <   io_pad_ring
  , input  arc_run_req_a                 //  <   io_pad_ring
  , input  [95:0] EventManager_evm_event_a //  <   apex_testbench.EventManager_tb
  , input  EventManager_evm_sleep        //  <   apex_testbench.EventManager_tb
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq17_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq19_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq21_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq22_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq23_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq24_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq25_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq26_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq27_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq28_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq29_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq30_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq31_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq32_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq33_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq34_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq35_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq36_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq37_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq38_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq39_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq40_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq41_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq42_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq43_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq44_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq45_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq46_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq47_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq48_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq49_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq50_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq51_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq52_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq53_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
// spyglass disable_block Ac_unsync01
// SMD: At least 2 bits of source bus are not uniformly synchronized to destination bus
// SJ:  
  , input  irq54_a                       //  <   alb_mss_ext_stub
// spyglass enable_block Ac_unsync01
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
  , input  presetdbgn                    //  <   clock_and_reset
  , input  [31:2] paddrdbg               //  <   fast_rascal
  , input  pseldbg                       //  <   fast_rascal
  , input  penabledbg                    //  <   fast_rascal
  , input  pwritedbg                     //  <   fast_rascal
  , input  [31:0] pwdatadbg              //  <   fast_rascal
  , input  dbgen                         //  <   fast_rascal
  , input  niden                         //  <   fast_rascal
  , input  dbg_cache_rst_disable         //  <   alb_mss_ext_stub
  , input  dccm_dmi_priority             //  <   alb_mss_ext_stub
  , input  [31:0] rtt_drd_r              //  <   rtt
  , input  rtt_prod_sel                  //  <   rtt
  , input  rtt_freeze                    //  <   rtt
  , input  [7:0] rtt_src_num             //  <   rtt
  , input  [7:0] arcnum /* verilator public_flat */ //  <   io_pad_ring
  , input  wdt_clk                       //  <   alb_mss_clkctrl
  , input  wdt_ext_timeout_ack_r         //  <   alb_mss_ext_stub
  , input  mem_ds                        //  <   alb_mss_ext_stub
  , input  mem_sd                        //  <   alb_mss_ext_stub
  , output rtt_write_a                   //    > rtt
  , output rtt_read_a                    //    > rtt
  , output [31:0] rtt_addr_r             //    > rtt
  , output [31:0] rtt_dwr_r              //    > rtt
  , output rtt_ss_halt                   //    > rtt
  , output rtt_hw_bp                     //    > rtt
  , output rtt_hw_exc                    //    > rtt
  , output rtt_dbg_halt                  //    > rtt
  , output rtt_rst_applied               //    > rtt
  , output rtt_uop_is_leave              //    > rtt
  , output rtt_in_deslot                 //    > rtt
  , output rtt_in_eslot                  //    > rtt
  , output rtt_inst_commit               //    > rtt
  , output [31:1] rtt_inst_addr          //    > rtt
  , output rtt_cond_valid                //    > rtt
  , output rtt_cond_pass                 //    > rtt
  , output rtt_branch                    //    > rtt
  , output rtt_branch_indir              //    > rtt
  , output [31:1] rtt_branch_taddr       //    > rtt
  , output rtt_dslot                     //    > rtt
  , output rtt_exception                 //    > rtt
  , output rtt_exception_rtn             //    > rtt
  , output rtt_interrupt                 //    > rtt
  , output rtt_sleep_mode                //    > rtt
  , output rtt_zd_loop                   //    > rtt
  , output [7:0] rtt_wp_val              //    > rtt
  , output rtt_wp_hit                    //    > rtt
  , output rtt_sw_bp                     //    > rtt
  , output sys_halt_r                    //    > rtt
  , output [7:0] rtt_process_id          //    > rtt
  , output rtt_pid_wr_en                 //    > rtt
  , output [32:0] rtt_swe_data           //    > rtt
  , output rtt_swe_val                   //    > rtt
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
  , output dbg_rerr                      //    > alb_mss_ext_stub
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
  , output dbg_cmdack                    //    > fast_rascal
  , output dbg_rspval                    //    > fast_rascal
  , output [31:0] dbg_rdata              //    > fast_rascal
  , output dbg_reop                      //    > fast_rascal
  , output preadydbg                     //    > fast_rascal
  , output [31:0] prdatadbg              //    > fast_rascal
  , output pslverrdbg                    //    > fast_rascal
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
wire   i_ifu_ibus_cmd_valid;             // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_cmd_valid
wire   [40-1:0] i_ifu_ibus_cmd_addr;     // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_cmd_addr [40-1:0]
wire   i_ifu_ibus_cmd_wrap;              // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_cmd_wrap
wire   [3:0] i_ifu_ibus_cmd_cache;       // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_cmd_cache [3:0]
wire   [3:0] i_ifu_ibus_cmd_burst_size;  // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_cmd_burst_size [3:0]
wire   [1:0] i_ifu_ibus_cmd_prot;        // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_cmd_prot [1:0]
wire   i_ifu_ibus_rd_accept;             // alb_cpu_top > cc_top -- alb_cpu_top.ifu_ibus_rd_accept
wire   i_lqwq_mem_cmd_valid;             // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_valid
wire   i_lqwq_mem_cmd_cache;             // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_cache
wire   i_lqwq_mem_cmd_read;              // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_read
wire   [39:0] i_lqwq_mem_cmd_addr;       // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_addr [39:0]
wire   i_lqwq_mem_cmd_burst_size;        // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_burst_size
wire   [2:0] i_lqwq_mem_cmd_data_size;   // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_data_size [2:0]
wire   i_lqwq_mem_cmd_lock;              // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_lock
wire   i_lqwq_mem_cmd_excl;              // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_excl
wire   [1:0] i_lqwq_mem_cmd_prot;        // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_cmd_prot [1:0]
wire   i_lqwq_mem_rd_accept;             // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_rd_accept
wire   i_lqwq_mem_wr_valid;              // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_wr_valid
wire   [63:0] i_lqwq_mem_wr_data;        // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_wr_data [63:0]
wire   [7:0] i_lqwq_mem_wr_mask;         // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_wr_mask [7:0]
wire   i_lqwq_mem_wr_last;               // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_wr_last
wire   i_lqwq_mem_wr_resp_accept;        // alb_cpu_top > cc_top -- alb_cpu_top.lqwq_mem_wr_resp_accept
wire   i_rf_cmd_valid;                   // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_valid
wire   i_rf_cmd_read;                    // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_read
wire   [39:0] i_rf_cmd_addr;             // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_addr [39:0]
wire   [1:0] i_rf_cmd_prot;              // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_prot [1:0]
wire   i_rf_cmd_wrap;                    // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_wrap
wire   [3:0] i_rf_cmd_burst_size;        // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_burst_size [3:0]
wire   [3:0] i_rf_cmd_cache;             // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_cache [3:0]
wire   i_rf_cmd_excl;                    // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_excl
wire   i_rf_cmd_lock;                    // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_lock
wire   [2:0] i_rf_cmd_data_size;         // alb_cpu_top > cc_top -- alb_cpu_top.rf_cmd_data_size [2:0]
wire   i_rf_rd_accept;                   // alb_cpu_top > cc_top -- alb_cpu_top.rf_rd_accept
wire   i_cb_cmd_valid;                   // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_valid
wire   i_cb_cmd_read;                    // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_read
wire   [39:0] i_cb_cmd_addr;             // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_addr [39:0]
wire   [1:0] i_cb_cmd_prot;              // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_prot [1:0]
wire   i_cb_cmd_wrap;                    // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_wrap
wire   [3:0] i_cb_cmd_burst_size;        // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_burst_size [3:0]
wire   [3:0] i_cb_cmd_cache;             // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_cache [3:0]
wire   i_cb_cmd_excl;                    // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_excl
wire   i_cb_cmd_lock;                    // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_lock
wire   [2:0] i_cb_cmd_data_size;         // alb_cpu_top > cc_top -- alb_cpu_top.cb_cmd_data_size [2:0]
wire   i_cb_wr_valid;                    // alb_cpu_top > cc_top -- alb_cpu_top.cb_wr_valid
wire   i_cb_wr_last;                     // alb_cpu_top > cc_top -- alb_cpu_top.cb_wr_last
wire   [127:0] i_cb_wr_data;             // alb_cpu_top > cc_top -- alb_cpu_top.cb_wr_data [127:0]
wire   [15:0] i_cb_wr_mask;              // alb_cpu_top > cc_top -- alb_cpu_top.cb_wr_mask [15:0]
wire   i_cb_wr_resp_accept;              // alb_cpu_top > cc_top -- alb_cpu_top.cb_wr_resp_accept
wire   i_dccm_dmi_cmd_accept;            // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_cmd_accept
wire   i_dccm_dmi_rd_valid;              // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_rd_valid
wire   i_dccm_dmi_err_rd;                // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_err_rd
wire   [63:0] i_dccm_dmi_rd_data;        // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_rd_data [63:0]
wire   i_dccm_dmi_wr_accept;             // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_wr_accept
wire   i_dccm_dmi_wr_done;               // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_wr_done
wire   i_dccm_dmi_err_wr;                // alb_cpu_top > cc_top -- alb_cpu_top.dccm_dmi_err_wr
wire   i_aux_rs_valid;                   // alb_cpu_top > cc_top -- alb_cpu_top.aux_rs_valid
wire   [11:0] i_aux_rs_addr;             // alb_cpu_top > cc_top -- alb_cpu_top.aux_rs_addr [11:0]
wire   [0:0] i_aux_rs_region;            // alb_cpu_top > cc_top -- alb_cpu_top.aux_rs_region [0:0]
wire   i_aux_rs_read;                    // alb_cpu_top > cc_top -- alb_cpu_top.aux_rs_read
wire   i_aux_rs_write;                   // alb_cpu_top > cc_top -- alb_cpu_top.aux_rs_write
wire   i_aux_wr_valid;                   // alb_cpu_top > cc_top -- alb_cpu_top.aux_wr_valid
wire   [11:0] i_aux_wr_addr;             // alb_cpu_top > cc_top -- alb_cpu_top.aux_wr_addr [11:0]
wire   [0:0] i_aux_wr_region;            // alb_cpu_top > cc_top -- alb_cpu_top.aux_wr_region [0:0]
wire   [31:0] i_aux_wr_data;             // alb_cpu_top > cc_top -- alb_cpu_top.aux_wr_data [31:0]
wire   i_aux_cm_phase;                   // alb_cpu_top > cc_top -- alb_cpu_top.aux_cm_phase
wire   i_aux_cm_valid;                   // alb_cpu_top > cc_top -- alb_cpu_top.aux_cm_valid
// spyglass disable_block Ac_conv02, Ac_conv03
// SMD: cdc synchronizers converging on combinational gates
// SJ:  cdc synchronizers are independent and chance of glitch are very low
wire   i_cpu_clk_enable;                 // alb_cpu_top > cc_top -- alb_cpu_top.cpu_clk_enable
// spyglass enable_block Ac_conv02, Ac_conv03
wire   i_biu_dmi_clk_en_req;             // cc_top > alb_cpu_top -- cc_top.biu_dmi_clk_en_req
wire   [`npuarc_CC_AUX_DATA_RANGE] i_aux_rs_data; // cc_top > alb_cpu_top -- cc_top.aux_rs_data [`npuarc_CC_AUX_DATA_RANGE]
wire   [`npuarc_CC_AUX_STAT_RANGE] i_aux_rs_status; // cc_top > alb_cpu_top -- cc_top.aux_rs_status [`npuarc_CC_AUX_STAT_RANGE]
wire   i_aux_rs_accept;                  // cc_top > alb_cpu_top -- cc_top.aux_rs_accept
wire   i_aux_wr_allow;                   // cc_top > alb_cpu_top -- cc_top.aux_wr_allow
wire   i_ifu_ibus_cmd_accept;            // cc_top > alb_cpu_top -- cc_top.ifu_ibus_cmd_accept
wire   i_ifu_ibus_rd_valid;              // cc_top > alb_cpu_top -- cc_top.ifu_ibus_rd_valid
wire   i_ifu_ibus_err_rd;                // cc_top > alb_cpu_top -- cc_top.ifu_ibus_err_rd
wire   [`npuarc_CC_BUS_RANGE] i_ifu_ibus_rd_data; // cc_top > alb_cpu_top -- cc_top.ifu_ibus_rd_data [`npuarc_CC_BUS_RANGE]
wire   i_ifu_ibus_rd_last;               // cc_top > alb_cpu_top -- cc_top.ifu_ibus_rd_last
wire   i_lqwq_mem_cmd_accept;            // cc_top > alb_cpu_top -- cc_top.lqwq_mem_cmd_accept
wire   i_lqwq_mem_wr_accept;             // cc_top > alb_cpu_top -- cc_top.lqwq_mem_wr_accept
wire   i_lqwq_mem_rd_valid;              // cc_top > alb_cpu_top -- cc_top.lqwq_mem_rd_valid
wire   i_lqwq_mem_err_rd;                // cc_top > alb_cpu_top -- cc_top.lqwq_mem_err_rd
wire   i_lqwq_mem_rd_excl_ok;            // cc_top > alb_cpu_top -- cc_top.lqwq_mem_rd_excl_ok
wire   i_lqwq_mem_rd_last;               // cc_top > alb_cpu_top -- cc_top.lqwq_mem_rd_last
wire   [`npuarc_CC_BUS_RANGE] i_lqwq_mem_rd_data; // cc_top > alb_cpu_top -- cc_top.lqwq_mem_rd_data [`npuarc_CC_BUS_RANGE]
wire   i_lqwq_mem_wr_done;               // cc_top > alb_cpu_top -- cc_top.lqwq_mem_wr_done
wire   i_lqwq_mem_wr_excl_done;          // cc_top > alb_cpu_top -- cc_top.lqwq_mem_wr_excl_done
wire   i_lqwq_mem_err_wr;                // cc_top > alb_cpu_top -- cc_top.lqwq_mem_err_wr
wire   i_rf_cmd_accept;                  // cc_top > alb_cpu_top -- cc_top.rf_cmd_accept
wire   i_rf_rd_valid;                    // cc_top > alb_cpu_top -- cc_top.rf_rd_valid
wire   i_rf_rd_last;                     // cc_top > alb_cpu_top -- cc_top.rf_rd_last
wire   i_rf_err_rd;                      // cc_top > alb_cpu_top -- cc_top.rf_err_rd
wire   [127:0] i_rf_rd_data;             // cc_top > alb_cpu_top -- cc_top.rf_rd_data [127:0]
wire   i_cb_cmd_accept;                  // cc_top > alb_cpu_top -- cc_top.cb_cmd_accept
wire   i_cb_wr_accept;                   // cc_top > alb_cpu_top -- cc_top.cb_wr_accept
wire   i_cb_wr_done;                     // cc_top > alb_cpu_top -- cc_top.cb_wr_done
wire   i_cb_err_wr;                      // cc_top > alb_cpu_top -- cc_top.cb_err_wr
wire   i_dccm_dmi_cmd_valid;             // cc_top > alb_cpu_top -- cc_top.dccm_dmi_cmd_valid
wire   i_dccm_dmi_cmd_read;              // cc_top > alb_cpu_top -- cc_top.dccm_dmi_cmd_read
wire   [24-1:3] i_dccm_dmi_cmd_addr;     // cc_top > alb_cpu_top -- cc_top.dccm_dmi_cmd_addr [24-1:3]
wire   i_dccm_dmi_rd_accept;             // cc_top > alb_cpu_top -- cc_top.dccm_dmi_rd_accept
wire   i_dccm_dmi_wr_valid;              // cc_top > alb_cpu_top -- cc_top.dccm_dmi_wr_valid
wire   [`npuarc_CC_DMI_BUS_RANGE] i_dccm_dmi_wr_data; // cc_top > alb_cpu_top -- cc_top.dccm_dmi_wr_data [`npuarc_CC_DMI_BUS_RANGE]
wire   [`npuarc_CC_DMI_MASK_RANGE] i_dccm_dmi_wr_mask; // cc_top > alb_cpu_top -- cc_top.dccm_dmi_wr_mask [`npuarc_CC_DMI_MASK_RANGE]
wire   [7:0] i_core_clusternum;          // cc_top > alb_cpu_top -- cc_top.core_clusternum [7:0]
wire   i_l1_cg_dis;                      // cc_top > alb_cpu_top -- cc_top.l1_cg_dis
wire   i_l1_accept_en;                   // cc_top > alb_cpu_top -- cc_top.l1_accept_en
wire   i_c0clk;                          // cc_top > alb_cpu_top -- cc_top.c0clk
// spyglass disable_block W287b
// SMD: port not connected
// SJ:  not connected in some configs
wire   i_clk_ungated;                    // cc_top > alb_cpu_top -- cc_top.clk_ungated
// spyglass enable_block W287b

// Instantiation of module cc_top
npuarc_cc_top icc_top(
    .ifu_ibus_cmd_valid      (i_ifu_ibus_cmd_valid) // <   alb_cpu_top
  , .ifu_ibus_cmd_addr       (i_ifu_ibus_cmd_addr) // <   alb_cpu_top
  , .ifu_ibus_cmd_wrap       (i_ifu_ibus_cmd_wrap) // <   alb_cpu_top
  , .ifu_ibus_cmd_cache      (i_ifu_ibus_cmd_cache) // <   alb_cpu_top
  , .ifu_ibus_cmd_burst_size (i_ifu_ibus_cmd_burst_size) // <   alb_cpu_top
  , .ifu_ibus_cmd_prot       (i_ifu_ibus_cmd_prot) // <   alb_cpu_top
  , .ifu_ibus_rd_accept      (i_ifu_ibus_rd_accept) // <   alb_cpu_top
  , .lqwq_mem_cmd_valid      (i_lqwq_mem_cmd_valid) // <   alb_cpu_top
  , .lqwq_mem_cmd_cache      (i_lqwq_mem_cmd_cache) // <   alb_cpu_top
  , .lqwq_mem_cmd_read       (i_lqwq_mem_cmd_read) // <   alb_cpu_top
  , .lqwq_mem_cmd_addr       (i_lqwq_mem_cmd_addr) // <   alb_cpu_top
  , .lqwq_mem_cmd_burst_size (i_lqwq_mem_cmd_burst_size) // <   alb_cpu_top
  , .lqwq_mem_cmd_data_size  (i_lqwq_mem_cmd_data_size) // <   alb_cpu_top
  , .lqwq_mem_cmd_lock       (i_lqwq_mem_cmd_lock) // <   alb_cpu_top
  , .lqwq_mem_cmd_excl       (i_lqwq_mem_cmd_excl) // <   alb_cpu_top
  , .lqwq_mem_cmd_prot       (i_lqwq_mem_cmd_prot) // <   alb_cpu_top
  , .lqwq_mem_rd_accept      (i_lqwq_mem_rd_accept) // <   alb_cpu_top
  , .lqwq_mem_wr_valid       (i_lqwq_mem_wr_valid) // <   alb_cpu_top
  , .lqwq_mem_wr_data        (i_lqwq_mem_wr_data)  // <   alb_cpu_top
  , .lqwq_mem_wr_mask        (i_lqwq_mem_wr_mask)  // <   alb_cpu_top
  , .lqwq_mem_wr_last        (i_lqwq_mem_wr_last)  // <   alb_cpu_top
  , .lqwq_mem_wr_resp_accept (i_lqwq_mem_wr_resp_accept) // <   alb_cpu_top
  , .rf_cmd_valid            (i_rf_cmd_valid)      // <   alb_cpu_top
  , .rf_cmd_read             (i_rf_cmd_read)       // <   alb_cpu_top
  , .rf_cmd_addr             (i_rf_cmd_addr)       // <   alb_cpu_top
  , .rf_cmd_prot             (i_rf_cmd_prot)       // <   alb_cpu_top
  , .rf_cmd_wrap             (i_rf_cmd_wrap)       // <   alb_cpu_top
  , .rf_cmd_burst_size       (i_rf_cmd_burst_size) // <   alb_cpu_top
  , .rf_cmd_cache            (i_rf_cmd_cache)      // <   alb_cpu_top
  , .rf_cmd_excl             (i_rf_cmd_excl)       // <   alb_cpu_top
  , .rf_cmd_lock             (i_rf_cmd_lock)       // <   alb_cpu_top
  , .rf_cmd_data_size        (i_rf_cmd_data_size)  // <   alb_cpu_top
  , .rf_rd_accept            (i_rf_rd_accept)      // <   alb_cpu_top
  , .cb_cmd_valid            (i_cb_cmd_valid)      // <   alb_cpu_top
  , .cb_cmd_read             (i_cb_cmd_read)       // <   alb_cpu_top
  , .cb_cmd_addr             (i_cb_cmd_addr)       // <   alb_cpu_top
  , .cb_cmd_prot             (i_cb_cmd_prot)       // <   alb_cpu_top
  , .cb_cmd_wrap             (i_cb_cmd_wrap)       // <   alb_cpu_top
  , .cb_cmd_burst_size       (i_cb_cmd_burst_size) // <   alb_cpu_top
  , .cb_cmd_cache            (i_cb_cmd_cache)      // <   alb_cpu_top
  , .cb_cmd_excl             (i_cb_cmd_excl)       // <   alb_cpu_top
  , .cb_cmd_lock             (i_cb_cmd_lock)       // <   alb_cpu_top
  , .cb_cmd_data_size        (i_cb_cmd_data_size)  // <   alb_cpu_top
  , .cb_wr_valid             (i_cb_wr_valid)       // <   alb_cpu_top
  , .cb_wr_last              (i_cb_wr_last)        // <   alb_cpu_top
  , .cb_wr_data              (i_cb_wr_data)        // <   alb_cpu_top
  , .cb_wr_mask              (i_cb_wr_mask)        // <   alb_cpu_top
  , .cb_wr_resp_accept       (i_cb_wr_resp_accept) // <   alb_cpu_top
  , .dccm_dmi_cmd_accept     (i_dccm_dmi_cmd_accept) // <   alb_cpu_top
  , .dccm_dmi_rd_valid       (i_dccm_dmi_rd_valid) // <   alb_cpu_top
  , .dccm_dmi_err_rd         (i_dccm_dmi_err_rd)   // <   alb_cpu_top
  , .dccm_dmi_rd_data        (i_dccm_dmi_rd_data)  // <   alb_cpu_top
  , .dccm_dmi_wr_accept      (i_dccm_dmi_wr_accept) // <   alb_cpu_top
  , .dccm_dmi_wr_done        (i_dccm_dmi_wr_done)  // <   alb_cpu_top
  , .dccm_dmi_err_wr         (i_dccm_dmi_err_wr)   // <   alb_cpu_top
  , .aux_rs_valid            (i_aux_rs_valid)      // <   alb_cpu_top
  , .aux_rs_addr             (i_aux_rs_addr)       // <   alb_cpu_top
  , .aux_rs_region           (i_aux_rs_region)     // <   alb_cpu_top
  , .aux_rs_read             (i_aux_rs_read)       // <   alb_cpu_top
  , .aux_rs_write            (i_aux_rs_write)      // <   alb_cpu_top
  , .aux_wr_valid            (i_aux_wr_valid)      // <   alb_cpu_top
  , .aux_wr_addr             (i_aux_wr_addr)       // <   alb_cpu_top
  , .aux_wr_region           (i_aux_wr_region)     // <   alb_cpu_top
  , .aux_wr_data             (i_aux_wr_data)       // <   alb_cpu_top
  , .aux_cm_phase            (i_aux_cm_phase)      // <   alb_cpu_top
  , .aux_cm_valid            (i_aux_cm_valid)      // <   alb_cpu_top
  , .cbu_axi_rid             (cbu_axi_rid)         // <   alb_mss_fab
  , .cbu_axi_arready         (cbu_axi_arready)     // <   alb_mss_fab
  , .cbu_axi_rvalid          (cbu_axi_rvalid)      // <   alb_mss_fab
  , .cbu_axi_rdata           (cbu_axi_rdata)       // <   alb_mss_fab
  , .cbu_axi_rresp           (cbu_axi_rresp)       // <   alb_mss_fab
  , .cbu_axi_rlast           (cbu_axi_rlast)       // <   alb_mss_fab
  , .cbu_axi_bid             (cbu_axi_bid)         // <   alb_mss_fab
  , .cbu_axi_awready         (cbu_axi_awready)     // <   alb_mss_fab
  , .cbu_axi_wready          (cbu_axi_wready)      // <   alb_mss_fab
  , .cbu_axi_bvalid          (cbu_axi_bvalid)      // <   alb_mss_fab
  , .cbu_axi_bresp           (cbu_axi_bresp)       // <   alb_mss_fab
  , .sccm_axi_arvalid        (sccm_axi_arvalid)    // <   alb_mss_fab
  , .sccm_axi_arid           (sccm_axi_arid)       // <   alb_mss_fab
  , .sccm_axi_araddr         (sccm_axi_araddr)     // <   alb_mss_fab
  , .sccm_axi_arregion       (sccm_axi_arregion)   // <   alb_mss_fab
  , .sccm_axi_arburst        (sccm_axi_arburst)    // <   alb_mss_fab
  , .sccm_axi_arlen          (sccm_axi_arlen)      // <   alb_mss_fab
  , .sccm_axi_arsize         (sccm_axi_arsize)     // <   alb_mss_fab
  , .sccm_axi_rready         (sccm_axi_rready)     // <   alb_mss_fab
  , .sccm_axi_awvalid        (sccm_axi_awvalid)    // <   alb_mss_fab
  , .sccm_axi_awid           (sccm_axi_awid)       // <   alb_mss_fab
  , .sccm_axi_awaddr         (sccm_axi_awaddr)     // <   alb_mss_fab
  , .sccm_axi_awregion       (sccm_axi_awregion)   // <   alb_mss_fab
  , .sccm_axi_awburst        (sccm_axi_awburst)    // <   alb_mss_fab
  , .sccm_axi_awlen          (sccm_axi_awlen)      // <   alb_mss_fab
  , .sccm_axi_awsize         (sccm_axi_awsize)     // <   alb_mss_fab
  , .sccm_axi_wvalid         (sccm_axi_wvalid)     // <   alb_mss_fab
  , .sccm_axi_wdata          (sccm_axi_wdata)      // <   alb_mss_fab
  , .sccm_axi_wstrb          (sccm_axi_wstrb)      // <   alb_mss_fab
  , .sccm_axi_wlast          (sccm_axi_wlast)      // <   alb_mss_fab
  , .sccm_axi_bready         (sccm_axi_bready)     // <   alb_mss_fab
  , .mbus_clk_en             (mbus_clk_en)         // <   alb_mss_clkctrl
  , .dbus_clk_en             (dbus_clk_en)         // <   alb_mss_clkctrl
// spyglass disable_block Ac_conv02, Ac_conv03
// SMD: cdc synchronizers converging on combinational gates
// SJ:  cdc synchronizers are independent and chance of glitch are very low
  , .cpu_clk_enable          (i_cpu_clk_enable)    // <   alb_cpu_top
// spyglass enable_block Ac_conv02, Ac_conv03
  , .clk                     (clk)                 // <   alb_mss_clkctrl
  , .rst_a                   (rst_a)               // <   io_pad_ring
  , .clusternum              (clusternum)          // <   io_pad_ring
  , .test_mode               (test_mode)           // <   io_pad_ring
  , .biu_dmi_clk_en_req      (i_biu_dmi_clk_en_req) //   > alb_cpu_top
  , .aux_rs_data             (i_aux_rs_data)       //   > alb_cpu_top
  , .aux_rs_status           (i_aux_rs_status)     //   > alb_cpu_top
  , .aux_rs_accept           (i_aux_rs_accept)     //   > alb_cpu_top
  , .aux_wr_allow            (i_aux_wr_allow)      //   > alb_cpu_top
  , .ifu_ibus_cmd_accept     (i_ifu_ibus_cmd_accept) //   > alb_cpu_top
  , .ifu_ibus_rd_valid       (i_ifu_ibus_rd_valid) //   > alb_cpu_top
  , .ifu_ibus_err_rd         (i_ifu_ibus_err_rd)   //   > alb_cpu_top
  , .ifu_ibus_rd_data        (i_ifu_ibus_rd_data)  //   > alb_cpu_top
  , .ifu_ibus_rd_last        (i_ifu_ibus_rd_last)  //   > alb_cpu_top
  , .lqwq_mem_cmd_accept     (i_lqwq_mem_cmd_accept) //   > alb_cpu_top
  , .lqwq_mem_wr_accept      (i_lqwq_mem_wr_accept) //   > alb_cpu_top
  , .lqwq_mem_rd_valid       (i_lqwq_mem_rd_valid) //   > alb_cpu_top
  , .lqwq_mem_err_rd         (i_lqwq_mem_err_rd)   //   > alb_cpu_top
  , .lqwq_mem_rd_excl_ok     (i_lqwq_mem_rd_excl_ok) //   > alb_cpu_top
  , .lqwq_mem_rd_last        (i_lqwq_mem_rd_last)  //   > alb_cpu_top
  , .lqwq_mem_rd_data        (i_lqwq_mem_rd_data)  //   > alb_cpu_top
  , .lqwq_mem_wr_done        (i_lqwq_mem_wr_done)  //   > alb_cpu_top
  , .lqwq_mem_wr_excl_done   (i_lqwq_mem_wr_excl_done) //   > alb_cpu_top
  , .lqwq_mem_err_wr         (i_lqwq_mem_err_wr)   //   > alb_cpu_top
  , .rf_cmd_accept           (i_rf_cmd_accept)     //   > alb_cpu_top
  , .rf_rd_valid             (i_rf_rd_valid)       //   > alb_cpu_top
  , .rf_rd_last              (i_rf_rd_last)        //   > alb_cpu_top
  , .rf_err_rd               (i_rf_err_rd)         //   > alb_cpu_top
  , .rf_rd_data              (i_rf_rd_data)        //   > alb_cpu_top
  , .cb_cmd_accept           (i_cb_cmd_accept)     //   > alb_cpu_top
  , .cb_wr_accept            (i_cb_wr_accept)      //   > alb_cpu_top
  , .cb_wr_done              (i_cb_wr_done)        //   > alb_cpu_top
  , .cb_err_wr               (i_cb_err_wr)         //   > alb_cpu_top
  , .dccm_dmi_cmd_valid      (i_dccm_dmi_cmd_valid) //   > alb_cpu_top
  , .dccm_dmi_cmd_read       (i_dccm_dmi_cmd_read) //   > alb_cpu_top
  , .dccm_dmi_cmd_addr       (i_dccm_dmi_cmd_addr) //   > alb_cpu_top
  , .dccm_dmi_rd_accept      (i_dccm_dmi_rd_accept) //   > alb_cpu_top
  , .dccm_dmi_wr_valid       (i_dccm_dmi_wr_valid) //   > alb_cpu_top
  , .dccm_dmi_wr_data        (i_dccm_dmi_wr_data)  //   > alb_cpu_top
  , .dccm_dmi_wr_mask        (i_dccm_dmi_wr_mask)  //   > alb_cpu_top
  , .core_clusternum         (i_core_clusternum)   //   > alb_cpu_top
  , .l1_cg_dis               (i_l1_cg_dis)         //   > alb_cpu_top
  , .l1_accept_en            (i_l1_accept_en)      //   > alb_cpu_top
  , .c0clk                   (i_c0clk)             //   > alb_cpu_top
// spyglass disable_block W287b
// SMD: port not connected
// SJ:  not connected in some configs
  , .clk_ungated             (i_clk_ungated)       //   > alb_cpu_top
// spyglass enable_block W287b
  , .cbu_axi_arid            (cbu_axi_arid)        //   > alb_mss_fab
  , .cbu_axi_arvalid         (cbu_axi_arvalid)     //   > alb_mss_fab
  , .cbu_axi_araddr          (cbu_axi_araddr)      //   > alb_mss_fab
  , .cbu_axi_arburst         (cbu_axi_arburst)     //   > alb_mss_fab
  , .cbu_axi_arsize          (cbu_axi_arsize)      //   > alb_mss_fab
  , .cbu_axi_arlock          (cbu_axi_arlock)      //   > alb_mss_fab
  , .cbu_axi_arlen           (cbu_axi_arlen)       //   > alb_mss_fab
  , .cbu_axi_arcache         (cbu_axi_arcache)     //   > alb_mss_fab
  , .cbu_axi_arprot          (cbu_axi_arprot)      //   > alb_mss_fab
  , .cbu_axi_rready          (cbu_axi_rready)      //   > alb_mss_fab
  , .cbu_axi_awid            (cbu_axi_awid)        //   > alb_mss_fab
  , .cbu_axi_awvalid         (cbu_axi_awvalid)     //   > alb_mss_fab
  , .cbu_axi_awaddr          (cbu_axi_awaddr)      //   > alb_mss_fab
  , .cbu_axi_awburst         (cbu_axi_awburst)     //   > alb_mss_fab
  , .cbu_axi_awsize          (cbu_axi_awsize)      //   > alb_mss_fab
  , .cbu_axi_awlock          (cbu_axi_awlock)      //   > alb_mss_fab
  , .cbu_axi_awlen           (cbu_axi_awlen)       //   > alb_mss_fab
  , .cbu_axi_awcache         (cbu_axi_awcache)     //   > alb_mss_fab
  , .cbu_axi_awprot          (cbu_axi_awprot)      //   > alb_mss_fab
  , .cbu_axi_wid             (cbu_axi_wid)         //   > alb_mss_fab
  , .cbu_axi_wvalid          (cbu_axi_wvalid)      //   > alb_mss_fab
  , .cbu_axi_wdata           (cbu_axi_wdata)       //   > alb_mss_fab
  , .cbu_axi_wstrb           (cbu_axi_wstrb)       //   > alb_mss_fab
  , .cbu_axi_wlast           (cbu_axi_wlast)       //   > alb_mss_fab
  , .cbu_axi_bready          (cbu_axi_bready)      //   > alb_mss_fab
  , .sccm_axi_arready        (sccm_axi_arready)    //   > alb_mss_fab
  , .sccm_axi_rid            (sccm_axi_rid)        //   > alb_mss_fab
  , .sccm_axi_rvalid         (sccm_axi_rvalid)     //   > alb_mss_fab
  , .sccm_axi_rdata          (sccm_axi_rdata)      //   > alb_mss_fab
  , .sccm_axi_rresp          (sccm_axi_rresp)      //   > alb_mss_fab
  , .sccm_axi_rlast          (sccm_axi_rlast)      //   > alb_mss_fab
  , .sccm_axi_awready        (sccm_axi_awready)    //   > alb_mss_fab
  , .sccm_axi_wready         (sccm_axi_wready)     //   > alb_mss_fab
  , .sccm_axi_bid            (sccm_axi_bid)        //   > alb_mss_fab
  , .sccm_axi_bvalid         (sccm_axi_bvalid)     //   > alb_mss_fab
  , .sccm_axi_bresp          (sccm_axi_bresp)      //   > alb_mss_fab
  , .cc_idle                 (cc_idle)             //   > alb_mss_ext_stub
  );

// Instantiation of module alb_cpu_top
npuarc_alb_cpu_top ialb_cpu_top(
    .arc_event_a               (arc_event_a)       // <   io_pad_ring
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
  , .biu_dmi_clk_en_req        (i_biu_dmi_clk_en_req) // <   cc_top
  , .aux_rs_data               (i_aux_rs_data)     // <   cc_top
  , .aux_rs_status             (i_aux_rs_status)   // <   cc_top
  , .aux_rs_accept             (i_aux_rs_accept)   // <   cc_top
  , .aux_wr_allow              (i_aux_wr_allow)    // <   cc_top
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
  , .rtt_drd_r                 (rtt_drd_r)         // <   rtt
  , .rtt_prod_sel              (rtt_prod_sel)      // <   rtt
  , .rtt_freeze                (rtt_freeze)        // <   rtt
  , .rtt_src_num               (rtt_src_num)       // <   rtt
  , .ifu_ibus_cmd_accept       (i_ifu_ibus_cmd_accept) // <   cc_top
  , .ifu_ibus_rd_valid         (i_ifu_ibus_rd_valid) // <   cc_top
  , .ifu_ibus_err_rd           (i_ifu_ibus_err_rd) // <   cc_top
  , .ifu_ibus_rd_data          (i_ifu_ibus_rd_data) // <   cc_top
  , .ifu_ibus_rd_last          (i_ifu_ibus_rd_last) // <   cc_top
  , .lqwq_mem_cmd_accept       (i_lqwq_mem_cmd_accept) // <   cc_top
  , .lqwq_mem_wr_accept        (i_lqwq_mem_wr_accept) // <   cc_top
  , .lqwq_mem_rd_valid         (i_lqwq_mem_rd_valid) // <   cc_top
  , .lqwq_mem_err_rd           (i_lqwq_mem_err_rd) // <   cc_top
  , .lqwq_mem_rd_excl_ok       (i_lqwq_mem_rd_excl_ok) // <   cc_top
  , .lqwq_mem_rd_last          (i_lqwq_mem_rd_last) // <   cc_top
  , .lqwq_mem_rd_data          (i_lqwq_mem_rd_data) // <   cc_top
  , .lqwq_mem_wr_done          (i_lqwq_mem_wr_done) // <   cc_top
  , .lqwq_mem_wr_excl_done     (i_lqwq_mem_wr_excl_done) // <   cc_top
  , .lqwq_mem_err_wr           (i_lqwq_mem_err_wr) // <   cc_top
  , .rf_cmd_accept             (i_rf_cmd_accept)   // <   cc_top
  , .rf_rd_valid               (i_rf_rd_valid)     // <   cc_top
  , .rf_rd_last                (i_rf_rd_last)      // <   cc_top
  , .rf_err_rd                 (i_rf_err_rd)       // <   cc_top
  , .rf_rd_data                (i_rf_rd_data)      // <   cc_top
  , .cb_cmd_accept             (i_cb_cmd_accept)   // <   cc_top
  , .cb_wr_accept              (i_cb_wr_accept)    // <   cc_top
  , .cb_wr_done                (i_cb_wr_done)      // <   cc_top
  , .cb_err_wr                 (i_cb_err_wr)       // <   cc_top
  , .dccm_dmi_cmd_valid        (i_dccm_dmi_cmd_valid) // <   cc_top
  , .dccm_dmi_cmd_read         (i_dccm_dmi_cmd_read) // <   cc_top
  , .dccm_dmi_cmd_addr         (i_dccm_dmi_cmd_addr) // <   cc_top
  , .dccm_dmi_rd_accept        (i_dccm_dmi_rd_accept) // <   cc_top
  , .dccm_dmi_wr_valid         (i_dccm_dmi_wr_valid) // <   cc_top
  , .dccm_dmi_wr_data          (i_dccm_dmi_wr_data) // <   cc_top
  , .dccm_dmi_wr_mask          (i_dccm_dmi_wr_mask) // <   cc_top
  , .test_mode                 (test_mode)         // <   io_pad_ring
  , .arcnum                    (arcnum)            // <   io_pad_ring
  , .core_clusternum           (i_core_clusternum) // <   cc_top
  , .wdt_clk                   (wdt_clk)           // <   alb_mss_clkctrl
  , .wdt_ext_timeout_ack_r     (wdt_ext_timeout_ack_r) // <   alb_mss_ext_stub
  , .mem_ds                    (mem_ds)            // <   alb_mss_ext_stub
  , .mem_sd                    (mem_sd)            // <   alb_mss_ext_stub
  , .l1_cg_dis                 (i_l1_cg_dis)       // <   cc_top
  , .l1_accept_en              (i_l1_accept_en)    // <   cc_top
  , .clk                       (i_c0clk)           // <   cc_top
// spyglass disable_block W287b
// SMD: port not connected
// SJ:  not connected in some configs
  , .clk_ungated               (i_clk_ungated)     // <   cc_top
// spyglass enable_block W287b
  , .rst_a                     (rst_a)             // <   io_pad_ring
  , .ifu_ibus_cmd_valid        (i_ifu_ibus_cmd_valid) //   > cc_top
  , .ifu_ibus_cmd_addr         (i_ifu_ibus_cmd_addr) //   > cc_top
  , .ifu_ibus_cmd_wrap         (i_ifu_ibus_cmd_wrap) //   > cc_top
  , .ifu_ibus_cmd_cache        (i_ifu_ibus_cmd_cache) //   > cc_top
  , .ifu_ibus_cmd_burst_size   (i_ifu_ibus_cmd_burst_size) //   > cc_top
  , .ifu_ibus_cmd_prot         (i_ifu_ibus_cmd_prot) //   > cc_top
  , .ifu_ibus_rd_accept        (i_ifu_ibus_rd_accept) //   > cc_top
  , .lqwq_mem_cmd_valid        (i_lqwq_mem_cmd_valid) //   > cc_top
  , .lqwq_mem_cmd_cache        (i_lqwq_mem_cmd_cache) //   > cc_top
  , .lqwq_mem_cmd_read         (i_lqwq_mem_cmd_read) //   > cc_top
  , .lqwq_mem_cmd_addr         (i_lqwq_mem_cmd_addr) //   > cc_top
  , .lqwq_mem_cmd_burst_size   (i_lqwq_mem_cmd_burst_size) //   > cc_top
  , .lqwq_mem_cmd_data_size    (i_lqwq_mem_cmd_data_size) //   > cc_top
  , .lqwq_mem_cmd_lock         (i_lqwq_mem_cmd_lock) //   > cc_top
  , .lqwq_mem_cmd_excl         (i_lqwq_mem_cmd_excl) //   > cc_top
  , .lqwq_mem_cmd_prot         (i_lqwq_mem_cmd_prot) //   > cc_top
  , .lqwq_mem_rd_accept        (i_lqwq_mem_rd_accept) //   > cc_top
  , .lqwq_mem_wr_valid         (i_lqwq_mem_wr_valid) //   > cc_top
  , .lqwq_mem_wr_data          (i_lqwq_mem_wr_data) //   > cc_top
  , .lqwq_mem_wr_mask          (i_lqwq_mem_wr_mask) //   > cc_top
  , .lqwq_mem_wr_last          (i_lqwq_mem_wr_last) //   > cc_top
  , .lqwq_mem_wr_resp_accept   (i_lqwq_mem_wr_resp_accept) //   > cc_top
  , .rf_cmd_valid              (i_rf_cmd_valid)    //   > cc_top
  , .rf_cmd_read               (i_rf_cmd_read)     //   > cc_top
  , .rf_cmd_addr               (i_rf_cmd_addr)     //   > cc_top
  , .rf_cmd_prot               (i_rf_cmd_prot)     //   > cc_top
  , .rf_cmd_wrap               (i_rf_cmd_wrap)     //   > cc_top
  , .rf_cmd_burst_size         (i_rf_cmd_burst_size) //   > cc_top
  , .rf_cmd_cache              (i_rf_cmd_cache)    //   > cc_top
  , .rf_cmd_excl               (i_rf_cmd_excl)     //   > cc_top
  , .rf_cmd_lock               (i_rf_cmd_lock)     //   > cc_top
  , .rf_cmd_data_size          (i_rf_cmd_data_size) //   > cc_top
  , .rf_rd_accept              (i_rf_rd_accept)    //   > cc_top
  , .cb_cmd_valid              (i_cb_cmd_valid)    //   > cc_top
  , .cb_cmd_read               (i_cb_cmd_read)     //   > cc_top
  , .cb_cmd_addr               (i_cb_cmd_addr)     //   > cc_top
  , .cb_cmd_prot               (i_cb_cmd_prot)     //   > cc_top
  , .cb_cmd_wrap               (i_cb_cmd_wrap)     //   > cc_top
  , .cb_cmd_burst_size         (i_cb_cmd_burst_size) //   > cc_top
  , .cb_cmd_cache              (i_cb_cmd_cache)    //   > cc_top
  , .cb_cmd_excl               (i_cb_cmd_excl)     //   > cc_top
  , .cb_cmd_lock               (i_cb_cmd_lock)     //   > cc_top
  , .cb_cmd_data_size          (i_cb_cmd_data_size) //   > cc_top
  , .cb_wr_valid               (i_cb_wr_valid)     //   > cc_top
  , .cb_wr_last                (i_cb_wr_last)      //   > cc_top
  , .cb_wr_data                (i_cb_wr_data)      //   > cc_top
  , .cb_wr_mask                (i_cb_wr_mask)      //   > cc_top
  , .cb_wr_resp_accept         (i_cb_wr_resp_accept) //   > cc_top
  , .dccm_dmi_cmd_accept       (i_dccm_dmi_cmd_accept) //   > cc_top
  , .dccm_dmi_rd_valid         (i_dccm_dmi_rd_valid) //   > cc_top
  , .dccm_dmi_err_rd           (i_dccm_dmi_err_rd) //   > cc_top
  , .dccm_dmi_rd_data          (i_dccm_dmi_rd_data) //   > cc_top
  , .dccm_dmi_wr_accept        (i_dccm_dmi_wr_accept) //   > cc_top
  , .dccm_dmi_wr_done          (i_dccm_dmi_wr_done) //   > cc_top
  , .dccm_dmi_err_wr           (i_dccm_dmi_err_wr) //   > cc_top
  , .aux_rs_valid              (i_aux_rs_valid)    //   > cc_top
  , .aux_rs_addr               (i_aux_rs_addr)     //   > cc_top
  , .aux_rs_region             (i_aux_rs_region)   //   > cc_top
  , .aux_rs_read               (i_aux_rs_read)     //   > cc_top
  , .aux_rs_write              (i_aux_rs_write)    //   > cc_top
  , .aux_wr_valid              (i_aux_wr_valid)    //   > cc_top
  , .aux_wr_addr               (i_aux_wr_addr)     //   > cc_top
  , .aux_wr_region             (i_aux_wr_region)   //   > cc_top
  , .aux_wr_data               (i_aux_wr_data)     //   > cc_top
  , .aux_cm_phase              (i_aux_cm_phase)    //   > cc_top
  , .aux_cm_valid              (i_aux_cm_valid)    //   > cc_top
// spyglass disable_block Ac_conv02, Ac_conv03
// SMD: cdc synchronizers converging on combinational gates
// SJ:  cdc synchronizers are independent and chance of glitch are very low
  , .cpu_clk_enable            (i_cpu_clk_enable)  //   > cc_top
// spyglass enable_block Ac_conv02, Ac_conv03
  , .rtt_write_a               (rtt_write_a)       //   > rtt
  , .rtt_read_a                (rtt_read_a)        //   > rtt
  , .rtt_addr_r                (rtt_addr_r)        //   > rtt
  , .rtt_dwr_r                 (rtt_dwr_r)         //   > rtt
  , .rtt_ss_halt               (rtt_ss_halt)       //   > rtt
  , .rtt_hw_bp                 (rtt_hw_bp)         //   > rtt
  , .rtt_hw_exc                (rtt_hw_exc)        //   > rtt
  , .rtt_dbg_halt              (rtt_dbg_halt)      //   > rtt
  , .rtt_rst_applied           (rtt_rst_applied)   //   > rtt
  , .rtt_uop_is_leave          (rtt_uop_is_leave)  //   > rtt
  , .rtt_in_deslot             (rtt_in_deslot)     //   > rtt
  , .rtt_in_eslot              (rtt_in_eslot)      //   > rtt
  , .rtt_inst_commit           (rtt_inst_commit)   //   > rtt
  , .rtt_inst_addr             (rtt_inst_addr)     //   > rtt
  , .rtt_cond_valid            (rtt_cond_valid)    //   > rtt
  , .rtt_cond_pass             (rtt_cond_pass)     //   > rtt
  , .rtt_branch                (rtt_branch)        //   > rtt
  , .rtt_branch_indir          (rtt_branch_indir)  //   > rtt
  , .rtt_branch_taddr          (rtt_branch_taddr)  //   > rtt
  , .rtt_dslot                 (rtt_dslot)         //   > rtt
  , .rtt_exception             (rtt_exception)     //   > rtt
  , .rtt_exception_rtn         (rtt_exception_rtn) //   > rtt
  , .rtt_interrupt             (rtt_interrupt)     //   > rtt
  , .rtt_sleep_mode            (rtt_sleep_mode)    //   > rtt
  , .rtt_zd_loop               (rtt_zd_loop)       //   > rtt
  , .rtt_wp_val                (rtt_wp_val)        //   > rtt
  , .rtt_wp_hit                (rtt_wp_hit)        //   > rtt
  , .rtt_sw_bp                 (rtt_sw_bp)         //   > rtt
  , .sys_halt_r                (sys_halt_r)        //   > rtt
  , .rtt_process_id            (rtt_process_id)    //   > rtt
  , .rtt_pid_wr_en             (rtt_pid_wr_en)     //   > rtt
  , .rtt_swe_data              (rtt_swe_data)      //   > rtt
  , .rtt_swe_val               (rtt_swe_val)       //   > rtt
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
endmodule
