// This file was automatically generated.
// Includes found in dependent files:
`include "npu_defines.v"
`include "arcsync_exported_defines.v"
`include "arcsync_defines.v"

module core_archipelago(
    input  npu_core_clk                  //  <   outside-of-hierarchy
  , input  npu_core_rst_a                //  <   outside-of-hierarchy
  , input  npu_noc_clk                   //  <   outside-of-hierarchy
  , input  npu_noc_rst_a                 //  <   outside-of-hierarchy
  , input  npu_cfg_clk                   //  <   outside-of-hierarchy
  , input  npu_cfg_rst_a                 //  <   outside-of-hierarchy
  , input  nl2arc0_wdt_clk               //  <   outside-of-hierarchy
  , input  nl2arc1_wdt_clk               //  <   outside-of-hierarchy
  , input  [39:24] npu_csm_base          //  <   outside-of-hierarchy
  , input  sl0_clk                       //  <   outside-of-hierarchy
  , input  sl0_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl1_clk                       //  <   outside-of-hierarchy
  , input  sl1_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl2_clk                       //  <   outside-of-hierarchy
  , input  sl2_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl3_clk                       //  <   outside-of-hierarchy
  , input  sl3_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl4_clk                       //  <   outside-of-hierarchy
  , input  sl4_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl5_clk                       //  <   outside-of-hierarchy
  , input  sl5_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl6_clk                       //  <   outside-of-hierarchy
  , input  sl6_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl7_clk                       //  <   outside-of-hierarchy
  , input  sl7_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl8_clk                       //  <   outside-of-hierarchy
  , input  sl8_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl9_clk                       //  <   outside-of-hierarchy
  , input  sl9_wdt_clk                   //  <   outside-of-hierarchy
  , input  sl10_clk                      //  <   outside-of-hierarchy
  , input  sl10_wdt_clk                  //  <   outside-of-hierarchy
  , input  sl11_clk                      //  <   outside-of-hierarchy
  , input  sl11_wdt_clk                  //  <   outside-of-hierarchy
  , input  sl12_clk                      //  <   outside-of-hierarchy
  , input  sl12_wdt_clk                  //  <   outside-of-hierarchy
  , input  sl13_clk                      //  <   outside-of-hierarchy
  , input  sl13_wdt_clk                  //  <   outside-of-hierarchy
  , input  sl14_clk                      //  <   outside-of-hierarchy
  , input  sl14_wdt_clk                  //  <   outside-of-hierarchy
  , input  sl15_clk                      //  <   outside-of-hierarchy
  , input  sl15_wdt_clk                  //  <   outside-of-hierarchy
  , input  npu_mst0_axi_arready          //  <   alb_mss_fab
  , input  npu_mst0_axi_rvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst0_axi_rid        //  <   alb_mss_fab
  , input  [63:0] npu_mst0_axi_rdata     //  <   alb_mss_fab
  , input  [1:0] npu_mst0_axi_rresp      //  <   alb_mss_fab
  , input  npu_mst0_axi_rlast            //  <   alb_mss_fab
  , input  npu_mst0_axi_awready          //  <   alb_mss_fab
  , input  npu_mst0_axi_wready           //  <   alb_mss_fab
  , input  npu_mst0_axi_bvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst0_axi_bid        //  <   alb_mss_fab
  , input  [1:0] npu_mst0_axi_bresp      //  <   alb_mss_fab
  , input  npu_mst1_axi_arready          //  <   alb_mss_fab
  , input  npu_mst1_axi_rvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst1_axi_rid        //  <   alb_mss_fab
  , input  [511:0] npu_mst1_axi_rdata    //  <   alb_mss_fab
  , input  [1:0] npu_mst1_axi_rresp      //  <   alb_mss_fab
  , input  npu_mst1_axi_rlast            //  <   alb_mss_fab
  , input  npu_mst1_axi_awready          //  <   alb_mss_fab
  , input  npu_mst1_axi_wready           //  <   alb_mss_fab
  , input  npu_mst1_axi_bvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst1_axi_bid        //  <   alb_mss_fab
  , input  [1:0] npu_mst1_axi_bresp      //  <   alb_mss_fab
  , input  npu_mst2_axi_arready          //  <   alb_mss_fab
  , input  npu_mst2_axi_rvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst2_axi_rid        //  <   alb_mss_fab
  , input  [511:0] npu_mst2_axi_rdata    //  <   alb_mss_fab
  , input  [1:0] npu_mst2_axi_rresp      //  <   alb_mss_fab
  , input  npu_mst2_axi_rlast            //  <   alb_mss_fab
  , input  npu_mst2_axi_awready          //  <   alb_mss_fab
  , input  npu_mst2_axi_wready           //  <   alb_mss_fab
  , input  npu_mst2_axi_bvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst2_axi_bid        //  <   alb_mss_fab
  , input  [1:0] npu_mst2_axi_bresp      //  <   alb_mss_fab
  , input  npu_mst3_axi_arready          //  <   alb_mss_fab
  , input  npu_mst3_axi_rvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst3_axi_rid        //  <   alb_mss_fab
  , input  [511:0] npu_mst3_axi_rdata    //  <   alb_mss_fab
  , input  [1:0] npu_mst3_axi_rresp      //  <   alb_mss_fab
  , input  npu_mst3_axi_rlast            //  <   alb_mss_fab
  , input  npu_mst3_axi_awready          //  <   alb_mss_fab
  , input  npu_mst3_axi_wready           //  <   alb_mss_fab
  , input  npu_mst3_axi_bvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst3_axi_bid        //  <   alb_mss_fab
  , input  [1:0] npu_mst3_axi_bresp      //  <   alb_mss_fab
  , input  npu_mst4_axi_arready          //  <   alb_mss_fab
  , input  npu_mst4_axi_rvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst4_axi_rid        //  <   alb_mss_fab
  , input  [511:0] npu_mst4_axi_rdata    //  <   alb_mss_fab
  , input  [1:0] npu_mst4_axi_rresp      //  <   alb_mss_fab
  , input  npu_mst4_axi_rlast            //  <   alb_mss_fab
  , input  npu_mst4_axi_awready          //  <   alb_mss_fab
  , input  npu_mst4_axi_wready           //  <   alb_mss_fab
  , input  npu_mst4_axi_bvalid           //  <   alb_mss_fab
  , input  [4:0] npu_mst4_axi_bid        //  <   alb_mss_fab
  , input  [1:0] npu_mst4_axi_bresp      //  <   alb_mss_fab
  , input  npu_dmi0_axi_arvalid          //  <   alb_mss_fab
  , input  [15:0] npu_dmi0_axi_arid      //  <   alb_mss_fab
  , input  [39:0] npu_dmi0_axi_araddr    //  <   alb_mss_fab
  , input  [3:0] npu_dmi0_axi_arcache    //  <   alb_mss_fab
  , input  [2:0] npu_dmi0_axi_arprot     //  <   alb_mss_fab
  , input  [0:0] npu_dmi0_axi_arlock     //  <   alb_mss_fab
  , input  [1:0] npu_dmi0_axi_arburst    //  <   alb_mss_fab
  , input  [3:0] npu_dmi0_axi_arlen      //  <   alb_mss_fab
  , input  [2:0] npu_dmi0_axi_arsize     //  <   alb_mss_fab
  , input  npu_dmi0_axi_rready           //  <   alb_mss_fab
  , input  npu_dmi0_axi_awvalid          //  <   alb_mss_fab
  , input  [15:0] npu_dmi0_axi_awid      //  <   alb_mss_fab
  , input  [39:0] npu_dmi0_axi_awaddr    //  <   alb_mss_fab
  , input  [3:0] npu_dmi0_axi_awcache    //  <   alb_mss_fab
  , input  [2:0] npu_dmi0_axi_awprot     //  <   alb_mss_fab
  , input  [0:0] npu_dmi0_axi_awlock     //  <   alb_mss_fab
  , input  [1:0] npu_dmi0_axi_awburst    //  <   alb_mss_fab
  , input  [3:0] npu_dmi0_axi_awlen      //  <   alb_mss_fab
  , input  [2:0] npu_dmi0_axi_awsize     //  <   alb_mss_fab
  , input  npu_dmi0_axi_wvalid           //  <   alb_mss_fab
  , input  [511:0] npu_dmi0_axi_wdata    //  <   alb_mss_fab
  , input  [63:0] npu_dmi0_axi_wstrb     //  <   alb_mss_fab
  , input  npu_dmi0_axi_wlast            //  <   alb_mss_fab
  , input  npu_dmi0_axi_bready           //  <   alb_mss_fab
  , input  npu_cfg_axi_arvalid           //  <   alb_mss_fab
  , input  [15:0] npu_cfg_axi_arid       //  <   alb_mss_fab
  , input  [39:0] npu_cfg_axi_araddr     //  <   alb_mss_fab
  , input  [3:0] npu_cfg_axi_arcache     //  <   alb_mss_fab
  , input  [2:0] npu_cfg_axi_arprot      //  <   alb_mss_fab
  , input  [0:0] npu_cfg_axi_arlock      //  <   alb_mss_fab
  , input  [1:0] npu_cfg_axi_arburst     //  <   alb_mss_fab
  , input  [3:0] npu_cfg_axi_arlen       //  <   alb_mss_fab
  , input  [2:0] npu_cfg_axi_arsize      //  <   alb_mss_fab
  , input  npu_cfg_axi_rready            //  <   alb_mss_fab
  , input  npu_cfg_axi_awvalid           //  <   alb_mss_fab
  , input  [15:0] npu_cfg_axi_awid       //  <   alb_mss_fab
  , input  [39:0] npu_cfg_axi_awaddr     //  <   alb_mss_fab
  , input  [3:0] npu_cfg_axi_awcache     //  <   alb_mss_fab
  , input  [2:0] npu_cfg_axi_awprot      //  <   alb_mss_fab
  , input  [0:0] npu_cfg_axi_awlock      //  <   alb_mss_fab
  , input  [1:0] npu_cfg_axi_awburst     //  <   alb_mss_fab
  , input  [3:0] npu_cfg_axi_awlen       //  <   alb_mss_fab
  , input  [2:0] npu_cfg_axi_awsize      //  <   alb_mss_fab
  , input  npu_cfg_axi_wvalid            //  <   alb_mss_fab
  , input  [31:0] npu_cfg_axi_wdata      //  <   alb_mss_fab
  , input  [3:0] npu_cfg_axi_wstrb       //  <   alb_mss_fab
  , input  npu_cfg_axi_wlast             //  <   alb_mss_fab
  , input  npu_cfg_axi_bready            //  <   alb_mss_fab
  , input  nl2arc_irq0_a                 //  <   outside-of-hierarchy
  , input  nl2arc_irq1_a                 //  <   outside-of-hierarchy
  , input  atclken                       //  <   outside-of-hierarchy
  , input  atresetn                      //  <   outside-of-hierarchy
  , input  [63:0] atb_cstimestamp        //  <   outside-of-hierarchy
  , input  atready                       //  <   outside-of-hierarchy
  , input  afvalid                       //  <   outside-of-hierarchy
  , input  syncreq                       //  <   outside-of-hierarchy
  , input  swe_atready                   //  <   outside-of-hierarchy
  , input  swe_afvalid                   //  <   outside-of-hierarchy
  , input  swe_syncreq                   //  <   outside-of-hierarchy
  , input  cti_trace_start               //  <   outside-of-hierarchy
  , input  cti_trace_stop                //  <   outside-of-hierarchy
  , input  pclkdbg                       //  <   outside-of-hierarchy
  , input  presetdbgn                    //  <   outside-of-hierarchy
  , input  [31:2] arct0_paddrdbg         //  <   outside-of-hierarchy
  , input  arct0_pseldbg                 //  <   outside-of-hierarchy
  , input  arct0_penabledbg              //  <   outside-of-hierarchy
  , input  arct0_pwritedbg               //  <   outside-of-hierarchy
  , input  [31:0] arct0_pwdatadbg        //  <   outside-of-hierarchy
  , input  arct0_dbgen                   //  <   outside-of-hierarchy
  , input  arct0_niden                   //  <   outside-of-hierarchy
  , input  sl0nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl0nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl1nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl1nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl2nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl2nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl3nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl3nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl4nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl4nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl5nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl5nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl6nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl6nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl7nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl7nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl8nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl8nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl9nl1arc_niden               //  <   outside-of-hierarchy
  , input  sl9nl1arc_dbgen               //  <   outside-of-hierarchy
  , input  sl10nl1arc_niden              //  <   outside-of-hierarchy
  , input  sl10nl1arc_dbgen              //  <   outside-of-hierarchy
  , input  sl11nl1arc_niden              //  <   outside-of-hierarchy
  , input  sl11nl1arc_dbgen              //  <   outside-of-hierarchy
  , input  sl12nl1arc_niden              //  <   outside-of-hierarchy
  , input  sl12nl1arc_dbgen              //  <   outside-of-hierarchy
  , input  sl13nl1arc_niden              //  <   outside-of-hierarchy
  , input  sl13nl1arc_dbgen              //  <   outside-of-hierarchy
  , input  sl14nl1arc_niden              //  <   outside-of-hierarchy
  , input  sl14nl1arc_dbgen              //  <   outside-of-hierarchy
  , input  sl15nl1arc_niden              //  <   outside-of-hierarchy
  , input  sl15nl1arc_dbgen              //  <   outside-of-hierarchy
  , input  nl2arc0_dbgen                 //  <   outside-of-hierarchy
  , input  nl2arc0_niden                 //  <   outside-of-hierarchy
  , input  nl2arc1_dbgen                 //  <   outside-of-hierarchy
  , input  nl2arc1_niden                 //  <   outside-of-hierarchy
  , input  test_mode                     //  <   outside-of-hierarchy
  , input  arcsync_axi_arvalid           //  <   alb_mss_fab
  , input  [15:0] arcsync_axi_arid       //  <   alb_mss_fab
  , input  [39:0] arcsync_axi_araddr     //  <   alb_mss_fab
  , input  [3:0] arcsync_axi_arcache     //  <   alb_mss_fab
  , input  [2:0] arcsync_axi_arprot      //  <   alb_mss_fab
  , input  [0:0] arcsync_axi_arlock      //  <   alb_mss_fab
  , input  [1:0] arcsync_axi_arburst     //  <   alb_mss_fab
  , input  [3:0] arcsync_axi_arlen       //  <   alb_mss_fab
  , input  [2:0] arcsync_axi_arsize      //  <   alb_mss_fab
  , input  arcsync_axi_rready            //  <   alb_mss_fab
  , input  arcsync_axi_awvalid           //  <   alb_mss_fab
  , input  [15:0] arcsync_axi_awid       //  <   alb_mss_fab
  , input  [39:0] arcsync_axi_awaddr     //  <   alb_mss_fab
  , input  [3:0] arcsync_axi_awcache     //  <   alb_mss_fab
  , input  [2:0] arcsync_axi_awprot      //  <   alb_mss_fab
  , input  [0:0] arcsync_axi_awlock      //  <   alb_mss_fab
  , input  [1:0] arcsync_axi_awburst     //  <   alb_mss_fab
  , input  [3:0] arcsync_axi_awlen       //  <   alb_mss_fab
  , input  [2:0] arcsync_axi_awsize      //  <   alb_mss_fab
  , input  arcsync_axi_wvalid            //  <   alb_mss_fab
  , input  [63:0] arcsync_axi_wdata      //  <   alb_mss_fab
  , input  [7:0] arcsync_axi_wstrb       //  <   alb_mss_fab
  , input  arcsync_axi_wlast             //  <   alb_mss_fab
  , input  arcsync_axi_bready            //  <   alb_mss_fab
  , input  nl2arc0_ext_arc_halt_req_a    //  <   outside-of-hierarchy
  , input  nl2arc0_ext_arc_run_req_a     //  <   outside-of-hierarchy
  , input  nl2arc1_ext_arc_halt_req_a    //  <   outside-of-hierarchy
  , input  nl2arc1_ext_arc_run_req_a     //  <   outside-of-hierarchy
  , input  sl0nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl0nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl1nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl1nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl2nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl2nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl3nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl3nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl4nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl4nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl5nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl5nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl6nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl6nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl7nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl7nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl8nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl8nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl9nl1arc_ext_arc_halt_req_a  //  <   outside-of-hierarchy
  , input  sl9nl1arc_ext_arc_run_req_a   //  <   outside-of-hierarchy
  , input  sl10nl1arc_ext_arc_halt_req_a //  <   outside-of-hierarchy
  , input  sl10nl1arc_ext_arc_run_req_a  //  <   outside-of-hierarchy
  , input  sl11nl1arc_ext_arc_halt_req_a //  <   outside-of-hierarchy
  , input  sl11nl1arc_ext_arc_run_req_a  //  <   outside-of-hierarchy
  , input  sl12nl1arc_ext_arc_halt_req_a //  <   outside-of-hierarchy
  , input  sl12nl1arc_ext_arc_run_req_a  //  <   outside-of-hierarchy
  , input  sl13nl1arc_ext_arc_halt_req_a //  <   outside-of-hierarchy
  , input  sl13nl1arc_ext_arc_run_req_a  //  <   outside-of-hierarchy
  , input  sl14nl1arc_ext_arc_halt_req_a //  <   outside-of-hierarchy
  , input  sl14nl1arc_ext_arc_run_req_a  //  <   outside-of-hierarchy
  , input  sl15nl1arc_ext_arc_halt_req_a //  <   outside-of-hierarchy
  , input  sl15nl1arc_ext_arc_run_req_a  //  <   outside-of-hierarchy
  , input  v0c0arc_halt_ack_a            //  <   arcsync_top_stub
  , input  v0c0ext_arc_halt_req_a        //  <   arcsync_top_stub
  , input  v0c0arc_run_ack_a             //  <   arcsync_top_stub
  , input  v0c0ext_arc_run_req_a         //  <   arcsync_top_stub
  , input  v0c0sys_sleep_r               //  <   arcsync_top_stub
  , input  [2:0] v0c0sys_sleep_mode_r    //  <   arcsync_top_stub
  , input  v0c0sys_halt_r                //  <   arcsync_top_stub
  , input  v0c0sys_tf_halt_r             //  <   arcsync_top_stub
  , input  [2:0] v0c0pmode               //  <   arcsync_top_stub
  , input  v0c1arc_halt_ack_a            //  <   arcsync_top_stub
  , input  v0c1ext_arc_halt_req_a        //  <   arcsync_top_stub
  , input  v0c1arc_run_ack_a             //  <   arcsync_top_stub
  , input  v0c1ext_arc_run_req_a         //  <   arcsync_top_stub
  , input  v0c1sys_sleep_r               //  <   arcsync_top_stub
  , input  [2:0] v0c1sys_sleep_mode_r    //  <   arcsync_top_stub
  , input  v0c1sys_halt_r                //  <   arcsync_top_stub
  , input  v0c1sys_tf_halt_r             //  <   arcsync_top_stub
  , input  [2:0] v0c1pmode               //  <   arcsync_top_stub
  , input  v0c2arc_halt_ack_a            //  <   arcsync_top_stub
  , input  v0c2ext_arc_halt_req_a        //  <   arcsync_top_stub
  , input  v0c2arc_run_ack_a             //  <   arcsync_top_stub
  , input  v0c2ext_arc_run_req_a         //  <   arcsync_top_stub
  , input  v0c2sys_sleep_r               //  <   arcsync_top_stub
  , input  [2:0] v0c2sys_sleep_mode_r    //  <   arcsync_top_stub
  , input  v0c2sys_halt_r                //  <   arcsync_top_stub
  , input  v0c2sys_tf_halt_r             //  <   arcsync_top_stub
  , input  [2:0] v0c2pmode               //  <   arcsync_top_stub
  , input  v0c3arc_halt_ack_a            //  <   arcsync_top_stub
  , input  v0c3ext_arc_halt_req_a        //  <   arcsync_top_stub
  , input  v0c3arc_run_ack_a             //  <   arcsync_top_stub
  , input  v0c3ext_arc_run_req_a         //  <   arcsync_top_stub
  , input  v0c3sys_sleep_r               //  <   arcsync_top_stub
  , input  [2:0] v0c3sys_sleep_mode_r    //  <   arcsync_top_stub
  , input  v0c3sys_halt_r                //  <   arcsync_top_stub
  , input  v0c3sys_tf_halt_r             //  <   arcsync_top_stub
  , input  [2:0] v0c3pmode               //  <   arcsync_top_stub
  , input  arcsync_axi_clk               //  <   outside-of-hierarchy
  , input  arcsync_axi_rst_a             //  <   outside-of-hierarchy
  , input  arcsync_core_iso_override     //  <   outside-of-hierarchy
  , input  arcsync_clk                   //  <   outside-of-hierarchy
  , input  arcsync_rst_a                 //  <   outside-of-hierarchy
  , output nl2arc_isolate_n              //    > arcsync_top_stub
  , output nl2arc_isolate                //    > arcsync_top_stub
  , output nl2arc_pd_mem                 //    > arcsync_top_stub
  , output nl2arc_pd_logic               //    > arcsync_top_stub
  , output nl2arc_pd_logic1              //    > arcsync_top_stub
  , output nl2arc_pd_logic2              //    > arcsync_top_stub
  , output grp0_isolate_n                //    > arcsync_top_stub
  , output grp0_isolate                  //    > arcsync_top_stub
  , output grp0_pd_mem                   //    > arcsync_top_stub
  , output grp0_pd_logic                 //    > arcsync_top_stub
  , output grp0_pd_logic1                //    > arcsync_top_stub
  , output grp0_pd_logic2                //    > arcsync_top_stub
  , output grp1_isolate_n                //    > arcsync_top_stub
  , output grp1_isolate                  //    > arcsync_top_stub
  , output grp1_pd_mem                   //    > arcsync_top_stub
  , output grp1_pd_logic                 //    > arcsync_top_stub
  , output grp1_pd_logic1                //    > arcsync_top_stub
  , output grp1_pd_logic2                //    > arcsync_top_stub
  , output grp2_isolate_n                //    > arcsync_top_stub
  , output grp2_isolate                  //    > arcsync_top_stub
  , output grp2_pd_mem                   //    > arcsync_top_stub
  , output grp2_pd_logic                 //    > arcsync_top_stub
  , output grp2_pd_logic1                //    > arcsync_top_stub
  , output grp2_pd_logic2                //    > arcsync_top_stub
  , output grp3_isolate_n                //    > arcsync_top_stub
  , output grp3_isolate                  //    > arcsync_top_stub
  , output grp3_pd_mem                   //    > arcsync_top_stub
  , output grp3_pd_logic                 //    > arcsync_top_stub
  , output grp3_pd_logic1                //    > arcsync_top_stub
  , output grp3_pd_logic2                //    > arcsync_top_stub
  , output sl0nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl0nl1arc_isolate             //    > arcsync_top_stub
  , output sl0nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl0nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl0nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl0nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl1nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl1nl1arc_isolate             //    > arcsync_top_stub
  , output sl1nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl1nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl1nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl1nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl2nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl2nl1arc_isolate             //    > arcsync_top_stub
  , output sl2nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl2nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl2nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl2nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl3nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl3nl1arc_isolate             //    > arcsync_top_stub
  , output sl3nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl3nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl3nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl3nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl4nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl4nl1arc_isolate             //    > arcsync_top_stub
  , output sl4nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl4nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl4nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl4nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl5nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl5nl1arc_isolate             //    > arcsync_top_stub
  , output sl5nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl5nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl5nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl5nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl6nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl6nl1arc_isolate             //    > arcsync_top_stub
  , output sl6nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl6nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl6nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl6nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl7nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl7nl1arc_isolate             //    > arcsync_top_stub
  , output sl7nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl7nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl7nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl7nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl8nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl8nl1arc_isolate             //    > arcsync_top_stub
  , output sl8nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl8nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl8nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl8nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl9nl1arc_isolate_n           //    > arcsync_top_stub
  , output sl9nl1arc_isolate             //    > arcsync_top_stub
  , output sl9nl1arc_pd_mem              //    > arcsync_top_stub
  , output sl9nl1arc_pd_logic            //    > arcsync_top_stub
  , output sl9nl1arc_pd_logic1           //    > arcsync_top_stub
  , output sl9nl1arc_pd_logic2           //    > arcsync_top_stub
  , output sl10nl1arc_isolate_n          //    > arcsync_top_stub
  , output sl10nl1arc_isolate            //    > arcsync_top_stub
  , output sl10nl1arc_pd_mem             //    > arcsync_top_stub
  , output sl10nl1arc_pd_logic           //    > arcsync_top_stub
  , output sl10nl1arc_pd_logic1          //    > arcsync_top_stub
  , output sl10nl1arc_pd_logic2          //    > arcsync_top_stub
  , output sl11nl1arc_isolate_n          //    > arcsync_top_stub
  , output sl11nl1arc_isolate            //    > arcsync_top_stub
  , output sl11nl1arc_pd_mem             //    > arcsync_top_stub
  , output sl11nl1arc_pd_logic           //    > arcsync_top_stub
  , output sl11nl1arc_pd_logic1          //    > arcsync_top_stub
  , output sl11nl1arc_pd_logic2          //    > arcsync_top_stub
  , output sl12nl1arc_isolate_n          //    > arcsync_top_stub
  , output sl12nl1arc_isolate            //    > arcsync_top_stub
  , output sl12nl1arc_pd_mem             //    > arcsync_top_stub
  , output sl12nl1arc_pd_logic           //    > arcsync_top_stub
  , output sl12nl1arc_pd_logic1          //    > arcsync_top_stub
  , output sl12nl1arc_pd_logic2          //    > arcsync_top_stub
  , output sl13nl1arc_isolate_n          //    > arcsync_top_stub
  , output sl13nl1arc_isolate            //    > arcsync_top_stub
  , output sl13nl1arc_pd_mem             //    > arcsync_top_stub
  , output sl13nl1arc_pd_logic           //    > arcsync_top_stub
  , output sl13nl1arc_pd_logic1          //    > arcsync_top_stub
  , output sl13nl1arc_pd_logic2          //    > arcsync_top_stub
  , output sl14nl1arc_isolate_n          //    > arcsync_top_stub
  , output sl14nl1arc_isolate            //    > arcsync_top_stub
  , output sl14nl1arc_pd_mem             //    > arcsync_top_stub
  , output sl14nl1arc_pd_logic           //    > arcsync_top_stub
  , output sl14nl1arc_pd_logic1          //    > arcsync_top_stub
  , output sl14nl1arc_pd_logic2          //    > arcsync_top_stub
  , output sl15nl1arc_isolate_n          //    > arcsync_top_stub
  , output sl15nl1arc_isolate            //    > arcsync_top_stub
  , output sl15nl1arc_pd_mem             //    > arcsync_top_stub
  , output sl15nl1arc_pd_logic           //    > arcsync_top_stub
  , output sl15nl1arc_pd_logic1          //    > arcsync_top_stub
  , output sl15nl1arc_pd_logic2          //    > arcsync_top_stub
  , output [39:16] v0csm_addr_base       //    > arcsync_top_stub
  , output [39:16] v0periph_addr_base    //    > arcsync_top_stub
  , output [7:0] v0clusternum            //    > arcsync_top_stub
  , output [7:0] v0c0arcnum              //    > arcsync_top_stub
  , output [31:10] v0c0intvbase          //    > arcsync_top_stub
  , output v0c0rst_a                     //    > arcsync_top_stub
  , output v0c0clk_en                    //    > arcsync_top_stub
  , output v0c0arc_halt_req              //    > arcsync_top_stub
  , output v0c0ext_arc_halt_ack          //    > arcsync_top_stub
  , output v0c0arc_run_req               //    > arcsync_top_stub
  , output v0c0ext_arc_run_ack           //    > arcsync_top_stub
  , output v0c0arc_irq0_a                //    > arcsync_top_stub
  , output v0c0arc_irq1_a                //    > arcsync_top_stub
  , output v0c0arc_event0_a              //    > arcsync_top_stub
  , output v0c0arc_event1_a              //    > arcsync_top_stub
  , output [7:0] v0c1arcnum              //    > arcsync_top_stub
  , output [31:10] v0c1intvbase          //    > arcsync_top_stub
  , output v0c1rst_a                     //    > arcsync_top_stub
  , output v0c1clk_en                    //    > arcsync_top_stub
  , output v0c1arc_halt_req              //    > arcsync_top_stub
  , output v0c1ext_arc_halt_ack          //    > arcsync_top_stub
  , output v0c1arc_run_req               //    > arcsync_top_stub
  , output v0c1ext_arc_run_ack           //    > arcsync_top_stub
  , output v0c1arc_irq0_a                //    > arcsync_top_stub
  , output v0c1arc_irq1_a                //    > arcsync_top_stub
  , output v0c1arc_event0_a              //    > arcsync_top_stub
  , output v0c1arc_event1_a              //    > arcsync_top_stub
  , output [7:0] v0c2arcnum              //    > arcsync_top_stub
  , output [31:10] v0c2intvbase          //    > arcsync_top_stub
  , output v0c2rst_a                     //    > arcsync_top_stub
  , output v0c2clk_en                    //    > arcsync_top_stub
  , output v0c2arc_halt_req              //    > arcsync_top_stub
  , output v0c2ext_arc_halt_ack          //    > arcsync_top_stub
  , output v0c2arc_run_req               //    > arcsync_top_stub
  , output v0c2ext_arc_run_ack           //    > arcsync_top_stub
  , output v0c2arc_irq0_a                //    > arcsync_top_stub
  , output v0c2arc_irq1_a                //    > arcsync_top_stub
  , output v0c2arc_event0_a              //    > arcsync_top_stub
  , output v0c2arc_event1_a              //    > arcsync_top_stub
  , output [7:0] v0c3arcnum              //    > arcsync_top_stub
  , output [31:10] v0c3intvbase          //    > arcsync_top_stub
  , output v0c3rst_a                     //    > arcsync_top_stub
  , output v0c3clk_en                    //    > arcsync_top_stub
  , output v0c3arc_halt_req              //    > arcsync_top_stub
  , output v0c3ext_arc_halt_ack          //    > arcsync_top_stub
  , output v0c3arc_run_req               //    > arcsync_top_stub
  , output v0c3ext_arc_run_ack           //    > arcsync_top_stub
  , output v0c3arc_irq0_a                //    > arcsync_top_stub
  , output v0c3arc_irq1_a                //    > arcsync_top_stub
  , output v0c3arc_event0_a              //    > arcsync_top_stub
  , output v0c3arc_event1_a              //    > arcsync_top_stub
  , output vpx_v0_vm0_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm0_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm0_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm0_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm1_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm1_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm1_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm1_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm2_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm2_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm2_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm2_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm3_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm3_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm3_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm3_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm4_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm4_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm4_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm4_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm5_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm5_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm5_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm5_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm6_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm6_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm6_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm6_evt_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm7_irq0_a             //    > arcsync_top_stub
  , output vpx_v0_vm7_irq_ac_a           //    > arcsync_top_stub
  , output vpx_v0_vm7_evt0_a             //    > arcsync_top_stub
  , output vpx_v0_vm7_evt_ac_a           //    > arcsync_top_stub
  , output v0c0_isolate_n                //    > arcsync_top_stub
  , output v0c0_isolate                  //    > arcsync_top_stub
  , output v0c0_pd_mem                   //    > arcsync_top_stub
  , output v0c0_pd_logic                 //    > arcsync_top_stub
  , output v0c0_pd_logic1                //    > arcsync_top_stub
  , output v0c0_pd_logic2                //    > arcsync_top_stub
  , output v0c1_isolate_n                //    > arcsync_top_stub
  , output v0c1_isolate                  //    > arcsync_top_stub
  , output v0c1_pd_mem                   //    > arcsync_top_stub
  , output v0c1_pd_logic                 //    > arcsync_top_stub
  , output v0c1_pd_logic1                //    > arcsync_top_stub
  , output v0c1_pd_logic2                //    > arcsync_top_stub
  , output v0c2_isolate_n                //    > arcsync_top_stub
  , output v0c2_isolate                  //    > arcsync_top_stub
  , output v0c2_pd_mem                   //    > arcsync_top_stub
  , output v0c2_pd_logic                 //    > arcsync_top_stub
  , output v0c2_pd_logic1                //    > arcsync_top_stub
  , output v0c2_pd_logic2                //    > arcsync_top_stub
  , output v0c3_isolate_n                //    > arcsync_top_stub
  , output v0c3_isolate                  //    > arcsync_top_stub
  , output v0c3_pd_mem                   //    > arcsync_top_stub
  , output v0c3_pd_logic                 //    > arcsync_top_stub
  , output v0c3_pd_logic1                //    > arcsync_top_stub
  , output v0c3_pd_logic2                //    > arcsync_top_stub
  , output [4:0] npu_mst0_axi_arid       //    > alb_mss_fab
  , output npu_mst0_axi_arvalid          //    > alb_mss_fab
  , output [39:0] npu_mst0_axi_araddr    //    > alb_mss_fab
  , output [1:0] npu_mst0_axi_arburst    //    > alb_mss_fab
  , output [2:0] npu_mst0_axi_arsize     //    > alb_mss_fab
  , output [0:0] npu_mst0_axi_arlock     //    > alb_mss_fab
  , output [3:0] npu_mst0_axi_arlen      //    > alb_mss_fab
  , output [3:0] npu_mst0_axi_arcache    //    > alb_mss_fab
  , output [2:0] npu_mst0_axi_arprot     //    > alb_mss_fab
  , output npu_mst0_axi_rready           //    > alb_mss_fab
  , output [4:0] npu_mst0_axi_awid       //    > alb_mss_fab
  , output npu_mst0_axi_awvalid          //    > alb_mss_fab
  , output [39:0] npu_mst0_axi_awaddr    //    > alb_mss_fab
  , output [1:0] npu_mst0_axi_awburst    //    > alb_mss_fab
  , output [2:0] npu_mst0_axi_awsize     //    > alb_mss_fab
  , output [0:0] npu_mst0_axi_awlock     //    > alb_mss_fab
  , output [3:0] npu_mst0_axi_awlen      //    > alb_mss_fab
  , output [3:0] npu_mst0_axi_awcache    //    > alb_mss_fab
  , output [2:0] npu_mst0_axi_awprot     //    > alb_mss_fab
  , output npu_mst0_axi_wvalid           //    > alb_mss_fab
  , output [63:0] npu_mst0_axi_wdata     //    > alb_mss_fab
  , output [7:0] npu_mst0_axi_wstrb      //    > alb_mss_fab
  , output npu_mst0_axi_wlast            //    > alb_mss_fab
  , output npu_mst0_axi_bready           //    > alb_mss_fab
  , output [4:0] npu_mst1_axi_arid       //    > alb_mss_fab
  , output npu_mst1_axi_arvalid          //    > alb_mss_fab
  , output [39:0] npu_mst1_axi_araddr    //    > alb_mss_fab
  , output [1:0] npu_mst1_axi_arburst    //    > alb_mss_fab
  , output [2:0] npu_mst1_axi_arsize     //    > alb_mss_fab
  , output [0:0] npu_mst1_axi_arlock     //    > alb_mss_fab
  , output [3:0] npu_mst1_axi_arlen      //    > alb_mss_fab
  , output [3:0] npu_mst1_axi_arcache    //    > alb_mss_fab
  , output [2:0] npu_mst1_axi_arprot     //    > alb_mss_fab
  , output npu_mst1_axi_rready           //    > alb_mss_fab
  , output [4:0] npu_mst1_axi_awid       //    > alb_mss_fab
  , output npu_mst1_axi_awvalid          //    > alb_mss_fab
  , output [39:0] npu_mst1_axi_awaddr    //    > alb_mss_fab
  , output [1:0] npu_mst1_axi_awburst    //    > alb_mss_fab
  , output [2:0] npu_mst1_axi_awsize     //    > alb_mss_fab
  , output [0:0] npu_mst1_axi_awlock     //    > alb_mss_fab
  , output [3:0] npu_mst1_axi_awlen      //    > alb_mss_fab
  , output [3:0] npu_mst1_axi_awcache    //    > alb_mss_fab
  , output [2:0] npu_mst1_axi_awprot     //    > alb_mss_fab
  , output npu_mst1_axi_wvalid           //    > alb_mss_fab
  , output [511:0] npu_mst1_axi_wdata    //    > alb_mss_fab
  , output [63:0] npu_mst1_axi_wstrb     //    > alb_mss_fab
  , output npu_mst1_axi_wlast            //    > alb_mss_fab
  , output npu_mst1_axi_bready           //    > alb_mss_fab
  , output [4:0] npu_mst2_axi_arid       //    > alb_mss_fab
  , output npu_mst2_axi_arvalid          //    > alb_mss_fab
  , output [39:0] npu_mst2_axi_araddr    //    > alb_mss_fab
  , output [1:0] npu_mst2_axi_arburst    //    > alb_mss_fab
  , output [2:0] npu_mst2_axi_arsize     //    > alb_mss_fab
  , output [0:0] npu_mst2_axi_arlock     //    > alb_mss_fab
  , output [3:0] npu_mst2_axi_arlen      //    > alb_mss_fab
  , output [3:0] npu_mst2_axi_arcache    //    > alb_mss_fab
  , output [2:0] npu_mst2_axi_arprot     //    > alb_mss_fab
  , output npu_mst2_axi_rready           //    > alb_mss_fab
  , output [4:0] npu_mst2_axi_awid       //    > alb_mss_fab
  , output npu_mst2_axi_awvalid          //    > alb_mss_fab
  , output [39:0] npu_mst2_axi_awaddr    //    > alb_mss_fab
  , output [1:0] npu_mst2_axi_awburst    //    > alb_mss_fab
  , output [2:0] npu_mst2_axi_awsize     //    > alb_mss_fab
  , output [0:0] npu_mst2_axi_awlock     //    > alb_mss_fab
  , output [3:0] npu_mst2_axi_awlen      //    > alb_mss_fab
  , output [3:0] npu_mst2_axi_awcache    //    > alb_mss_fab
  , output [2:0] npu_mst2_axi_awprot     //    > alb_mss_fab
  , output npu_mst2_axi_wvalid           //    > alb_mss_fab
  , output [511:0] npu_mst2_axi_wdata    //    > alb_mss_fab
  , output [63:0] npu_mst2_axi_wstrb     //    > alb_mss_fab
  , output npu_mst2_axi_wlast            //    > alb_mss_fab
  , output npu_mst2_axi_bready           //    > alb_mss_fab
  , output [4:0] npu_mst3_axi_arid       //    > alb_mss_fab
  , output npu_mst3_axi_arvalid          //    > alb_mss_fab
  , output [39:0] npu_mst3_axi_araddr    //    > alb_mss_fab
  , output [1:0] npu_mst3_axi_arburst    //    > alb_mss_fab
  , output [2:0] npu_mst3_axi_arsize     //    > alb_mss_fab
  , output [0:0] npu_mst3_axi_arlock     //    > alb_mss_fab
  , output [3:0] npu_mst3_axi_arlen      //    > alb_mss_fab
  , output [3:0] npu_mst3_axi_arcache    //    > alb_mss_fab
  , output [2:0] npu_mst3_axi_arprot     //    > alb_mss_fab
  , output npu_mst3_axi_rready           //    > alb_mss_fab
  , output [4:0] npu_mst3_axi_awid       //    > alb_mss_fab
  , output npu_mst3_axi_awvalid          //    > alb_mss_fab
  , output [39:0] npu_mst3_axi_awaddr    //    > alb_mss_fab
  , output [1:0] npu_mst3_axi_awburst    //    > alb_mss_fab
  , output [2:0] npu_mst3_axi_awsize     //    > alb_mss_fab
  , output [0:0] npu_mst3_axi_awlock     //    > alb_mss_fab
  , output [3:0] npu_mst3_axi_awlen      //    > alb_mss_fab
  , output [3:0] npu_mst3_axi_awcache    //    > alb_mss_fab
  , output [2:0] npu_mst3_axi_awprot     //    > alb_mss_fab
  , output npu_mst3_axi_wvalid           //    > alb_mss_fab
  , output [511:0] npu_mst3_axi_wdata    //    > alb_mss_fab
  , output [63:0] npu_mst3_axi_wstrb     //    > alb_mss_fab
  , output npu_mst3_axi_wlast            //    > alb_mss_fab
  , output npu_mst3_axi_bready           //    > alb_mss_fab
  , output [4:0] npu_mst4_axi_arid       //    > alb_mss_fab
  , output npu_mst4_axi_arvalid          //    > alb_mss_fab
  , output [39:0] npu_mst4_axi_araddr    //    > alb_mss_fab
  , output [1:0] npu_mst4_axi_arburst    //    > alb_mss_fab
  , output [2:0] npu_mst4_axi_arsize     //    > alb_mss_fab
  , output [0:0] npu_mst4_axi_arlock     //    > alb_mss_fab
  , output [3:0] npu_mst4_axi_arlen      //    > alb_mss_fab
  , output [3:0] npu_mst4_axi_arcache    //    > alb_mss_fab
  , output [2:0] npu_mst4_axi_arprot     //    > alb_mss_fab
  , output npu_mst4_axi_rready           //    > alb_mss_fab
  , output [4:0] npu_mst4_axi_awid       //    > alb_mss_fab
  , output npu_mst4_axi_awvalid          //    > alb_mss_fab
  , output [39:0] npu_mst4_axi_awaddr    //    > alb_mss_fab
  , output [1:0] npu_mst4_axi_awburst    //    > alb_mss_fab
  , output [2:0] npu_mst4_axi_awsize     //    > alb_mss_fab
  , output [0:0] npu_mst4_axi_awlock     //    > alb_mss_fab
  , output [3:0] npu_mst4_axi_awlen      //    > alb_mss_fab
  , output [3:0] npu_mst4_axi_awcache    //    > alb_mss_fab
  , output [2:0] npu_mst4_axi_awprot     //    > alb_mss_fab
  , output npu_mst4_axi_wvalid           //    > alb_mss_fab
  , output [511:0] npu_mst4_axi_wdata    //    > alb_mss_fab
  , output [63:0] npu_mst4_axi_wstrb     //    > alb_mss_fab
  , output npu_mst4_axi_wlast            //    > alb_mss_fab
  , output npu_mst4_axi_bready           //    > alb_mss_fab
  , output npu_dmi0_axi_arready          //    > alb_mss_fab
  , output [15:0] npu_dmi0_axi_rid       //    > alb_mss_fab
  , output npu_dmi0_axi_rvalid           //    > alb_mss_fab
  , output [511:0] npu_dmi0_axi_rdata    //    > alb_mss_fab
  , output [1:0] npu_dmi0_axi_rresp      //    > alb_mss_fab
  , output npu_dmi0_axi_rlast            //    > alb_mss_fab
  , output npu_dmi0_axi_awready          //    > alb_mss_fab
  , output npu_dmi0_axi_wready           //    > alb_mss_fab
  , output [15:0] npu_dmi0_axi_bid       //    > alb_mss_fab
  , output npu_dmi0_axi_bvalid           //    > alb_mss_fab
  , output [1:0] npu_dmi0_axi_bresp      //    > alb_mss_fab
  , output npu_cfg_axi_arready           //    > alb_mss_fab
  , output [15:0] npu_cfg_axi_rid        //    > alb_mss_fab
  , output npu_cfg_axi_rvalid            //    > alb_mss_fab
  , output [31:0] npu_cfg_axi_rdata      //    > alb_mss_fab
  , output [1:0] npu_cfg_axi_rresp       //    > alb_mss_fab
  , output npu_cfg_axi_rlast             //    > alb_mss_fab
  , output npu_cfg_axi_awready           //    > alb_mss_fab
  , output npu_cfg_axi_wready            //    > alb_mss_fab
  , output [15:0] npu_cfg_axi_bid        //    > alb_mss_fab
  , output npu_cfg_axi_bvalid            //    > alb_mss_fab
  , output [1:0] npu_cfg_axi_bresp       //    > alb_mss_fab
  , output arcsync_axi_arready           //    > alb_mss_fab
  , output [15:0] arcsync_axi_rid        //    > alb_mss_fab
  , output arcsync_axi_rvalid            //    > alb_mss_fab
  , output [63:0] arcsync_axi_rdata      //    > alb_mss_fab
  , output [1:0] arcsync_axi_rresp       //    > alb_mss_fab
  , output arcsync_axi_rlast             //    > alb_mss_fab
  , output arcsync_axi_awready           //    > alb_mss_fab
  , output arcsync_axi_wready            //    > alb_mss_fab
  , output [15:0] arcsync_axi_bid        //    > alb_mss_fab
  , output arcsync_axi_bvalid            //    > alb_mss_fab
  , output [1:0] arcsync_axi_bresp       //    > alb_mss_fab
  , output [31:0] npu_mst1_axi_arsid     //    > core_sys_stub
  , output [31:0] npu_mst1_axi_arssid    //    > core_sys_stub
  , output [31:0] npu_mst1_axi_awsid     //    > core_sys_stub
  , output [31:0] npu_mst1_axi_awssid    //    > core_sys_stub
  , output [31:0] npu_mst2_axi_arsid     //    > core_sys_stub
  , output [31:0] npu_mst2_axi_arssid    //    > core_sys_stub
  , output [31:0] npu_mst2_axi_awsid     //    > core_sys_stub
  , output [31:0] npu_mst2_axi_awssid    //    > core_sys_stub
  , output [31:0] npu_mst3_axi_arsid     //    > core_sys_stub
  , output [31:0] npu_mst3_axi_arssid    //    > core_sys_stub
  , output [31:0] npu_mst3_axi_awsid     //    > core_sys_stub
  , output [31:0] npu_mst3_axi_awssid    //    > core_sys_stub
  , output [31:0] npu_mst4_axi_arsid     //    > core_sys_stub
  , output [31:0] npu_mst4_axi_arssid    //    > core_sys_stub
  , output [31:0] npu_mst4_axi_awsid     //    > core_sys_stub
  , output [31:0] npu_mst4_axi_awssid    //    > core_sys_stub
  , output sl0_ecc_sbe                   //    > core_sys_stub
  , output sl0_ecc_dbe                   //    > core_sys_stub
  , output sl1_ecc_sbe                   //    > core_sys_stub
  , output sl1_ecc_dbe                   //    > core_sys_stub
  , output sl2_ecc_sbe                   //    > core_sys_stub
  , output sl2_ecc_dbe                   //    > core_sys_stub
  , output sl3_ecc_sbe                   //    > core_sys_stub
  , output sl3_ecc_dbe                   //    > core_sys_stub
  , output sl4_ecc_sbe                   //    > core_sys_stub
  , output sl4_ecc_dbe                   //    > core_sys_stub
  , output sl5_ecc_sbe                   //    > core_sys_stub
  , output sl5_ecc_dbe                   //    > core_sys_stub
  , output sl6_ecc_sbe                   //    > core_sys_stub
  , output sl6_ecc_dbe                   //    > core_sys_stub
  , output sl7_ecc_sbe                   //    > core_sys_stub
  , output sl7_ecc_dbe                   //    > core_sys_stub
  , output sl8_ecc_sbe                   //    > core_sys_stub
  , output sl8_ecc_dbe                   //    > core_sys_stub
  , output sl9_ecc_sbe                   //    > core_sys_stub
  , output sl9_ecc_dbe                   //    > core_sys_stub
  , output sl10_ecc_sbe                  //    > core_sys_stub
  , output sl10_ecc_dbe                  //    > core_sys_stub
  , output sl11_ecc_sbe                  //    > core_sys_stub
  , output sl11_ecc_dbe                  //    > core_sys_stub
  , output sl12_ecc_sbe                  //    > core_sys_stub
  , output sl12_ecc_dbe                  //    > core_sys_stub
  , output sl13_ecc_sbe                  //    > core_sys_stub
  , output sl13_ecc_dbe                  //    > core_sys_stub
  , output sl14_ecc_sbe                  //    > core_sys_stub
  , output sl14_ecc_dbe                  //    > core_sys_stub
  , output sl15_ecc_sbe                  //    > core_sys_stub
  , output sl15_ecc_dbe                  //    > core_sys_stub
  , output grp0_scm_dbank_sbe            //    > core_sys_stub
  , output grp0_scm_dbank_dbe            //    > core_sys_stub
  , output grp1_scm_dbank_sbe            //    > core_sys_stub
  , output grp1_scm_dbank_dbe            //    > core_sys_stub
  , output grp2_scm_dbank_sbe            //    > core_sys_stub
  , output grp2_scm_dbank_dbe            //    > core_sys_stub
  , output grp3_scm_dbank_sbe            //    > core_sys_stub
  , output grp3_scm_dbank_dbe            //    > core_sys_stub
  , output nl2arc0_ecc_sbe               //    > core_sys_stub
  , output nl2arc0_ecc_dbe               //    > core_sys_stub
  , output nl2arc1_ecc_sbe               //    > core_sys_stub
  , output nl2arc1_ecc_dbe               //    > core_sys_stub
  , output nl2arc0_evt_vm_irq            //    > outside-of-hierarchy
  , output nl2arc1_evt_vm_irq            //    > outside-of-hierarchy
  , output [63:0] atdata                 //    > outside-of-hierarchy
  , output [2:0] atbytes                 //    > outside-of-hierarchy
  , output [6:0] atid                    //    > outside-of-hierarchy
  , output atvalid                       //    > outside-of-hierarchy
  , output afready                       //    > outside-of-hierarchy
  , output [63:0] swe_atdata             //    > outside-of-hierarchy
  , output [2:0] swe_atbytes             //    > outside-of-hierarchy
  , output [6:0] swe_atid                //    > outside-of-hierarchy
  , output swe_atvalid                   //    > outside-of-hierarchy
  , output swe_afready                   //    > outside-of-hierarchy
  , output [25:0] cti_rtt_filters        //    > outside-of-hierarchy
  , output arct0_preadydbg               //    > outside-of-hierarchy
  , output [31:0] arct0_prdatadbg        //    > outside-of-hierarchy
  , output arct0_pslverrdbg              //    > outside-of-hierarchy
  , output nl2arc0_ext_arc_run_ack       //    > outside-of-hierarchy
  , output nl2arc0_ext_arc_halt_ack      //    > outside-of-hierarchy
  , output nl2arc1_ext_arc_run_ack       //    > outside-of-hierarchy
  , output nl2arc1_ext_arc_halt_ack      //    > outside-of-hierarchy
  , output sl0nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl0nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl1nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl1nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl2nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl2nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl3nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl3nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl4nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl4nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl5nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl5nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl6nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl6nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl7nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl7nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl8nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl8nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl9nl1arc_ext_arc_run_ack     //    > outside-of-hierarchy
  , output sl9nl1arc_ext_arc_halt_ack    //    > outside-of-hierarchy
  , output sl10nl1arc_ext_arc_run_ack    //    > outside-of-hierarchy
  , output sl10nl1arc_ext_arc_halt_ack   //    > outside-of-hierarchy
  , output sl11nl1arc_ext_arc_run_ack    //    > outside-of-hierarchy
  , output sl11nl1arc_ext_arc_halt_ack   //    > outside-of-hierarchy
  , output sl12nl1arc_ext_arc_run_ack    //    > outside-of-hierarchy
  , output sl12nl1arc_ext_arc_halt_ack   //    > outside-of-hierarchy
  , output sl13nl1arc_ext_arc_run_ack    //    > outside-of-hierarchy
  , output sl13nl1arc_ext_arc_halt_ack   //    > outside-of-hierarchy
  , output sl14nl1arc_ext_arc_run_ack    //    > outside-of-hierarchy
  , output sl14nl1arc_ext_arc_halt_ack   //    > outside-of-hierarchy
  , output sl15nl1arc_ext_arc_run_ack    //    > outside-of-hierarchy
  , output sl15nl1arc_ext_arc_halt_ack   //    > outside-of-hierarchy
  , output [1:0] h0host_irq              //    > outside-of-hierarchy
  , output [1:0] h0host_event            //    > outside-of-hierarchy
  , output [15:0] h0host_virt_evt_a      //    > outside-of-hierarchy
  , output [15:0] h0host_virt_irq_a      //    > outside-of-hierarchy
  );

// Intermediate signals:
wire   i_grp0_rst_a;                     // arcsync_top > npu_top -- arcsync_top.grp0_rst_a
wire   i_grp0_clk_en;                    // arcsync_top > npu_top -- arcsync_top.grp0_clk_en
wire   i_grp1_rst_a;                     // arcsync_top > npu_top -- arcsync_top.grp1_rst_a
wire   i_grp1_clk_en;                    // arcsync_top > npu_top -- arcsync_top.grp1_clk_en
wire   i_grp2_rst_a;                     // arcsync_top > npu_top -- arcsync_top.grp2_rst_a
wire   i_grp2_clk_en;                    // arcsync_top > npu_top -- arcsync_top.grp2_clk_en
wire   i_grp3_rst_a;                     // arcsync_top > npu_top -- arcsync_top.grp3_rst_a
wire   i_grp3_clk_en;                    // arcsync_top > npu_top -- arcsync_top.grp3_clk_en
wire   i_sl0_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl0_rst_a
wire   i_sl0_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl0_clk_en_a
wire   i_sl1_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl1_rst_a
wire   i_sl1_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl1_clk_en_a
wire   i_sl2_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl2_rst_a
wire   i_sl2_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl2_clk_en_a
wire   i_sl3_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl3_rst_a
wire   i_sl3_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl3_clk_en_a
wire   i_sl4_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl4_rst_a
wire   i_sl4_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl4_clk_en_a
wire   i_sl5_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl5_rst_a
wire   i_sl5_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl5_clk_en_a
wire   i_sl6_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl6_rst_a
wire   i_sl6_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl6_clk_en_a
wire   i_sl7_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl7_rst_a
wire   i_sl7_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl7_clk_en_a
wire   i_sl8_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl8_rst_a
wire   i_sl8_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl8_clk_en_a
wire   i_sl9_rst_a;                      // arcsync_top > npu_top -- arcsync_top.sl9_rst_a
wire   i_sl9_clk_en_a;                   // arcsync_top > npu_top -- arcsync_top.sl9_clk_en_a
wire   i_sl10_rst_a;                     // arcsync_top > npu_top -- arcsync_top.sl10_rst_a
wire   i_sl10_clk_en_a;                  // arcsync_top > npu_top -- arcsync_top.sl10_clk_en_a
wire   i_sl11_rst_a;                     // arcsync_top > npu_top -- arcsync_top.sl11_rst_a
wire   i_sl11_clk_en_a;                  // arcsync_top > npu_top -- arcsync_top.sl11_clk_en_a
wire   i_sl12_rst_a;                     // arcsync_top > npu_top -- arcsync_top.sl12_rst_a
wire   i_sl12_clk_en_a;                  // arcsync_top > npu_top -- arcsync_top.sl12_clk_en_a
wire   i_sl13_rst_a;                     // arcsync_top > npu_top -- arcsync_top.sl13_rst_a
wire   i_sl13_clk_en_a;                  // arcsync_top > npu_top -- arcsync_top.sl13_clk_en_a
wire   i_sl14_rst_a;                     // arcsync_top > npu_top -- arcsync_top.sl14_rst_a
wire   i_sl14_clk_en_a;                  // arcsync_top > npu_top -- arcsync_top.sl14_clk_en_a
wire   i_sl15_rst_a;                     // arcsync_top > npu_top -- arcsync_top.sl15_rst_a
wire   i_sl15_clk_en_a;                  // arcsync_top > npu_top -- arcsync_top.sl15_clk_en_a
wire   i_nl2arc0_rst_a;                  // arcsync_top > npu_top -- arcsync_top.nl2arc0_rst_a
wire   i_nl2arc0_clk_en_a;               // arcsync_top > npu_top -- arcsync_top.nl2arc0_clk_en_a
wire   i_nl2arc1_rst_a;                  // arcsync_top > npu_top -- arcsync_top.nl2arc1_rst_a
wire   i_nl2arc1_clk_en_a;               // arcsync_top > npu_top -- arcsync_top.nl2arc1_clk_en_a
wire   i_nl2_rst_a;                      // arcsync_top > npu_top -- arcsync_top.nl2_rst_a
wire   i_nl2arc_pwr_dwn;                 // arcsync_top > npu_top -- arcsync_top.nl2arc_pwr_dwn
wire   i_nl2arc0_pwr_dwn;                // arcsync_top > npu_top -- arcsync_top.nl2arc0_pwr_dwn
wire   i_nl2arc1_pwr_dwn;                // arcsync_top > npu_top -- arcsync_top.nl2arc1_pwr_dwn
wire   i_grp0_pwr_dwn;                   // arcsync_top > npu_top -- arcsync_top.grp0_pwr_dwn
wire   i_grp1_pwr_dwn;                   // arcsync_top > npu_top -- arcsync_top.grp1_pwr_dwn
wire   i_grp2_pwr_dwn;                   // arcsync_top > npu_top -- arcsync_top.grp2_pwr_dwn
wire   i_grp3_pwr_dwn;                   // arcsync_top > npu_top -- arcsync_top.grp3_pwr_dwn
wire   i_sl0nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_pwr_dwn
wire   i_sl1nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_pwr_dwn
wire   i_sl2nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_pwr_dwn
wire   i_sl3nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_pwr_dwn
wire   i_sl4nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_pwr_dwn
wire   i_sl5nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_pwr_dwn
wire   i_sl6nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_pwr_dwn
wire   i_sl7nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_pwr_dwn
wire   i_sl8nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_pwr_dwn
wire   i_sl9nl1arc_pwr_dwn;              // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_pwr_dwn
wire   i_sl10nl1arc_pwr_dwn;             // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_pwr_dwn
wire   i_sl11nl1arc_pwr_dwn;             // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_pwr_dwn
wire   i_sl12nl1arc_pwr_dwn;             // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_pwr_dwn
wire   i_sl13nl1arc_pwr_dwn;             // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_pwr_dwn
wire   i_sl14nl1arc_pwr_dwn;             // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_pwr_dwn
wire   i_sl15nl1arc_pwr_dwn;             // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_pwr_dwn
wire   i_nl2arc_isolate_n;               // arcsync_top > npu_top -- arcsync_top.nl2arc_isolate_n
wire   i_nl2arc_isolate;                 // arcsync_top > npu_top -- arcsync_top.nl2arc_isolate
wire   i_nl2arc_pd_mem;                  // arcsync_top > npu_top -- arcsync_top.nl2arc_pd_mem
wire   i_nl2arc_pd_logic;                // arcsync_top > npu_top -- arcsync_top.nl2arc_pd_logic
wire   i_grp0_isolate_n;                 // arcsync_top > npu_top -- arcsync_top.grp0_isolate_n
wire   i_grp0_isolate;                   // arcsync_top > npu_top -- arcsync_top.grp0_isolate
wire   i_grp0_pd_mem;                    // arcsync_top > npu_top -- arcsync_top.grp0_pd_mem
wire   i_grp0_pd_logic;                  // arcsync_top > npu_top -- arcsync_top.grp0_pd_logic
wire   i_grp1_isolate_n;                 // arcsync_top > npu_top -- arcsync_top.grp1_isolate_n
wire   i_grp1_isolate;                   // arcsync_top > npu_top -- arcsync_top.grp1_isolate
wire   i_grp1_pd_mem;                    // arcsync_top > npu_top -- arcsync_top.grp1_pd_mem
wire   i_grp1_pd_logic;                  // arcsync_top > npu_top -- arcsync_top.grp1_pd_logic
wire   i_grp2_isolate_n;                 // arcsync_top > npu_top -- arcsync_top.grp2_isolate_n
wire   i_grp2_isolate;                   // arcsync_top > npu_top -- arcsync_top.grp2_isolate
wire   i_grp2_pd_mem;                    // arcsync_top > npu_top -- arcsync_top.grp2_pd_mem
wire   i_grp2_pd_logic;                  // arcsync_top > npu_top -- arcsync_top.grp2_pd_logic
wire   i_grp3_isolate_n;                 // arcsync_top > npu_top -- arcsync_top.grp3_isolate_n
wire   i_grp3_isolate;                   // arcsync_top > npu_top -- arcsync_top.grp3_isolate
wire   i_grp3_pd_mem;                    // arcsync_top > npu_top -- arcsync_top.grp3_pd_mem
wire   i_grp3_pd_logic;                  // arcsync_top > npu_top -- arcsync_top.grp3_pd_logic
wire   i_sl0nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_isolate_n
wire   i_sl0nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_isolate
wire   i_sl0nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_pd_mem
wire   i_sl0nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_pd_logic
wire   i_sl1nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_isolate_n
wire   i_sl1nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_isolate
wire   i_sl1nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_pd_mem
wire   i_sl1nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_pd_logic
wire   i_sl2nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_isolate_n
wire   i_sl2nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_isolate
wire   i_sl2nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_pd_mem
wire   i_sl2nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_pd_logic
wire   i_sl3nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_isolate_n
wire   i_sl3nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_isolate
wire   i_sl3nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_pd_mem
wire   i_sl3nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_pd_logic
wire   i_sl4nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_isolate_n
wire   i_sl4nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_isolate
wire   i_sl4nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_pd_mem
wire   i_sl4nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_pd_logic
wire   i_sl5nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_isolate_n
wire   i_sl5nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_isolate
wire   i_sl5nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_pd_mem
wire   i_sl5nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_pd_logic
wire   i_sl6nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_isolate_n
wire   i_sl6nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_isolate
wire   i_sl6nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_pd_mem
wire   i_sl6nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_pd_logic
wire   i_sl7nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_isolate_n
wire   i_sl7nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_isolate
wire   i_sl7nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_pd_mem
wire   i_sl7nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_pd_logic
wire   i_sl8nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_isolate_n
wire   i_sl8nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_isolate
wire   i_sl8nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_pd_mem
wire   i_sl8nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_pd_logic
wire   i_sl9nl1arc_isolate_n;            // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_isolate_n
wire   i_sl9nl1arc_isolate;              // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_isolate
wire   i_sl9nl1arc_pd_mem;               // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_pd_mem
wire   i_sl9nl1arc_pd_logic;             // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_pd_logic
wire   i_sl10nl1arc_isolate_n;           // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_isolate_n
wire   i_sl10nl1arc_isolate;             // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_isolate
wire   i_sl10nl1arc_pd_mem;              // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_pd_mem
wire   i_sl10nl1arc_pd_logic;            // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_pd_logic
wire   i_sl11nl1arc_isolate_n;           // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_isolate_n
wire   i_sl11nl1arc_isolate;             // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_isolate
wire   i_sl11nl1arc_pd_mem;              // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_pd_mem
wire   i_sl11nl1arc_pd_logic;            // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_pd_logic
wire   i_sl12nl1arc_isolate_n;           // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_isolate_n
wire   i_sl12nl1arc_isolate;             // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_isolate
wire   i_sl12nl1arc_pd_mem;              // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_pd_mem
wire   i_sl12nl1arc_pd_logic;            // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_pd_logic
wire   i_sl13nl1arc_isolate_n;           // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_isolate_n
wire   i_sl13nl1arc_isolate;             // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_isolate
wire   i_sl13nl1arc_pd_mem;              // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_pd_mem
wire   i_sl13nl1arc_pd_logic;            // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_pd_logic
wire   i_sl14nl1arc_isolate_n;           // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_isolate_n
wire   i_sl14nl1arc_isolate;             // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_isolate
wire   i_sl14nl1arc_pd_mem;              // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_pd_mem
wire   i_sl14nl1arc_pd_logic;            // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_pd_logic
wire   i_sl15nl1arc_isolate_n;           // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_isolate_n
wire   i_sl15nl1arc_isolate;             // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_isolate
wire   i_sl15nl1arc_pd_mem;              // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_pd_mem
wire   i_sl15nl1arc_pd_logic;            // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_pd_logic
wire   [31:10] i_nl2arc0_intvbase_in;    // arcsync_top > npu_top -- arcsync_top.nl2arc0_intvbase_in [31:10]
wire   i_nl2arc0_arc_halt_req;           // arcsync_top > npu_top -- arcsync_top.nl2arc0_arc_halt_req
wire   i_nl2arc0_arc_run_req;            // arcsync_top > npu_top -- arcsync_top.nl2arc0_arc_run_req
wire   [17:0] i_nl2arc0_arc_irq_a;       // arcsync_top > npu_top -- arcsync_top.nl2arc0_arc_irq_a [17:0]
wire   [17:0] i_nl2arc0_arc_event_a;     // arcsync_top > npu_top -- arcsync_top.nl2arc0_arc_event_a [17:0]
wire   [31:10] i_nl2arc1_intvbase_in;    // arcsync_top > npu_top -- arcsync_top.nl2arc1_intvbase_in [31:10]
wire   i_nl2arc1_arc_halt_req;           // arcsync_top > npu_top -- arcsync_top.nl2arc1_arc_halt_req
wire   i_nl2arc1_arc_run_req;            // arcsync_top > npu_top -- arcsync_top.nl2arc1_arc_run_req
wire   [17:0] i_nl2arc1_arc_irq_a;       // arcsync_top > npu_top -- arcsync_top.nl2arc1_arc_irq_a [17:0]
wire   [17:0] i_nl2arc1_arc_event_a;     // arcsync_top > npu_top -- arcsync_top.nl2arc1_arc_event_a [17:0]
wire   [31:10] i_sl0nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_intvbase_in [31:10]
wire   i_sl0nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_arc_halt_req
wire   i_sl0nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_arc_run_req
wire   [1:0] i_sl0nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl0nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl1nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_intvbase_in [31:10]
wire   i_sl1nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_arc_halt_req
wire   i_sl1nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_arc_run_req
wire   [1:0] i_sl1nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl1nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl2nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_intvbase_in [31:10]
wire   i_sl2nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_arc_halt_req
wire   i_sl2nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_arc_run_req
wire   [1:0] i_sl2nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl2nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl3nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_intvbase_in [31:10]
wire   i_sl3nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_arc_halt_req
wire   i_sl3nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_arc_run_req
wire   [1:0] i_sl3nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl3nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl4nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_intvbase_in [31:10]
wire   i_sl4nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_arc_halt_req
wire   i_sl4nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_arc_run_req
wire   [1:0] i_sl4nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl4nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl5nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_intvbase_in [31:10]
wire   i_sl5nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_arc_halt_req
wire   i_sl5nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_arc_run_req
wire   [1:0] i_sl5nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl5nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl6nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_intvbase_in [31:10]
wire   i_sl6nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_arc_halt_req
wire   i_sl6nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_arc_run_req
wire   [1:0] i_sl6nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl6nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl7nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_intvbase_in [31:10]
wire   i_sl7nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_arc_halt_req
wire   i_sl7nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_arc_run_req
wire   [1:0] i_sl7nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl7nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl8nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_intvbase_in [31:10]
wire   i_sl8nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_arc_halt_req
wire   i_sl8nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_arc_run_req
wire   [1:0] i_sl8nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl8nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl9nl1arc_intvbase_in;  // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_intvbase_in [31:10]
wire   i_sl9nl1arc_arc_halt_req;         // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_arc_halt_req
wire   i_sl9nl1arc_arc_run_req;          // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_arc_run_req
wire   [1:0] i_sl9nl1arc_arc_irq_a;      // arcsync_top > npu_top -- arcsync_top.sl9nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl10nl1arc_intvbase_in; // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_intvbase_in [31:10]
wire   i_sl10nl1arc_arc_halt_req;        // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_arc_halt_req
wire   i_sl10nl1arc_arc_run_req;         // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_arc_run_req
wire   [1:0] i_sl10nl1arc_arc_irq_a;     // arcsync_top > npu_top -- arcsync_top.sl10nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl11nl1arc_intvbase_in; // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_intvbase_in [31:10]
wire   i_sl11nl1arc_arc_halt_req;        // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_arc_halt_req
wire   i_sl11nl1arc_arc_run_req;         // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_arc_run_req
wire   [1:0] i_sl11nl1arc_arc_irq_a;     // arcsync_top > npu_top -- arcsync_top.sl11nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl12nl1arc_intvbase_in; // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_intvbase_in [31:10]
wire   i_sl12nl1arc_arc_halt_req;        // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_arc_halt_req
wire   i_sl12nl1arc_arc_run_req;         // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_arc_run_req
wire   [1:0] i_sl12nl1arc_arc_irq_a;     // arcsync_top > npu_top -- arcsync_top.sl12nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl13nl1arc_intvbase_in; // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_intvbase_in [31:10]
wire   i_sl13nl1arc_arc_halt_req;        // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_arc_halt_req
wire   i_sl13nl1arc_arc_run_req;         // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_arc_run_req
wire   [1:0] i_sl13nl1arc_arc_irq_a;     // arcsync_top > npu_top -- arcsync_top.sl13nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl14nl1arc_intvbase_in; // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_intvbase_in [31:10]
wire   i_sl14nl1arc_arc_halt_req;        // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_arc_halt_req
wire   i_sl14nl1arc_arc_run_req;         // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_arc_run_req
wire   [1:0] i_sl14nl1arc_arc_irq_a;     // arcsync_top > npu_top -- arcsync_top.sl14nl1arc_arc_irq_a [1:0]
wire   [31:10] i_sl15nl1arc_intvbase_in; // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_intvbase_in [31:10]
wire   i_sl15nl1arc_arc_halt_req;        // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_arc_halt_req
wire   i_sl15nl1arc_arc_run_req;         // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_arc_run_req
wire   [1:0] i_sl15nl1arc_arc_irq_a;     // arcsync_top > npu_top -- arcsync_top.sl15nl1arc_arc_irq_a [1:0]
wire   [7:0] i_nl2arc0_clusternum;       // arcsync_top > npu_top -- arcsync_top.nl2arc0_clusternum [7:0]
wire   i_nl2arc0_arc_halt_ack;           // npu_top > arcsync_top -- npu_top.nl2arc0_arc_halt_ack
wire   i_nl2arc0_arc_run_ack;            // npu_top > arcsync_top -- npu_top.nl2arc0_arc_run_ack
wire   i_nl2arc0_sys_sleep_r;            // npu_top > arcsync_top -- npu_top.nl2arc0_sys_sleep_r
wire   [2:0] i_nl2arc0_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.nl2arc0_sys_sleep_mode_r [2:0]
wire   i_nl2arc0_sys_halt_r;             // npu_top > arcsync_top -- npu_top.nl2arc0_sys_halt_r
wire   i_nl2arc0_sys_tf_halt_r;          // npu_top > arcsync_top -- npu_top.nl2arc0_sys_tf_halt_r
wire   i_nl2arc1_arc_halt_ack;           // npu_top > arcsync_top -- npu_top.nl2arc1_arc_halt_ack
wire   i_nl2arc1_arc_run_ack;            // npu_top > arcsync_top -- npu_top.nl2arc1_arc_run_ack
wire   i_nl2arc1_sys_sleep_r;            // npu_top > arcsync_top -- npu_top.nl2arc1_sys_sleep_r
wire   [2:0] i_nl2arc1_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.nl2arc1_sys_sleep_mode_r [2:0]
wire   i_nl2arc1_sys_halt_r;             // npu_top > arcsync_top -- npu_top.nl2arc1_sys_halt_r
wire   i_nl2arc1_sys_tf_halt_r;          // npu_top > arcsync_top -- npu_top.nl2arc1_sys_tf_halt_r
wire   i_sl0nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl0nl1arc_arc_halt_ack
wire   i_sl0nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl0nl1arc_arc_run_ack
wire   i_sl0nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl0nl1arc_sys_sleep_r
wire   [2:0] i_sl0nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl0nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl0nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl0nl1arc_sys_halt_r
wire   i_sl0nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl0nl1arc_sys_tf_halt_r
wire   i_sl1nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl1nl1arc_arc_halt_ack
wire   i_sl1nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl1nl1arc_arc_run_ack
wire   i_sl1nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl1nl1arc_sys_sleep_r
wire   [2:0] i_sl1nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl1nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl1nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl1nl1arc_sys_halt_r
wire   i_sl1nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl1nl1arc_sys_tf_halt_r
wire   i_sl2nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl2nl1arc_arc_halt_ack
wire   i_sl2nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl2nl1arc_arc_run_ack
wire   i_sl2nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl2nl1arc_sys_sleep_r
wire   [2:0] i_sl2nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl2nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl2nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl2nl1arc_sys_halt_r
wire   i_sl2nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl2nl1arc_sys_tf_halt_r
wire   i_sl3nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl3nl1arc_arc_halt_ack
wire   i_sl3nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl3nl1arc_arc_run_ack
wire   i_sl3nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl3nl1arc_sys_sleep_r
wire   [2:0] i_sl3nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl3nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl3nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl3nl1arc_sys_halt_r
wire   i_sl3nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl3nl1arc_sys_tf_halt_r
wire   i_sl4nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl4nl1arc_arc_halt_ack
wire   i_sl4nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl4nl1arc_arc_run_ack
wire   i_sl4nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl4nl1arc_sys_sleep_r
wire   [2:0] i_sl4nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl4nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl4nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl4nl1arc_sys_halt_r
wire   i_sl4nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl4nl1arc_sys_tf_halt_r
wire   i_sl5nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl5nl1arc_arc_halt_ack
wire   i_sl5nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl5nl1arc_arc_run_ack
wire   i_sl5nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl5nl1arc_sys_sleep_r
wire   [2:0] i_sl5nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl5nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl5nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl5nl1arc_sys_halt_r
wire   i_sl5nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl5nl1arc_sys_tf_halt_r
wire   i_sl6nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl6nl1arc_arc_halt_ack
wire   i_sl6nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl6nl1arc_arc_run_ack
wire   i_sl6nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl6nl1arc_sys_sleep_r
wire   [2:0] i_sl6nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl6nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl6nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl6nl1arc_sys_halt_r
wire   i_sl6nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl6nl1arc_sys_tf_halt_r
wire   i_sl7nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl7nl1arc_arc_halt_ack
wire   i_sl7nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl7nl1arc_arc_run_ack
wire   i_sl7nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl7nl1arc_sys_sleep_r
wire   [2:0] i_sl7nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl7nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl7nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl7nl1arc_sys_halt_r
wire   i_sl7nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl7nl1arc_sys_tf_halt_r
wire   i_sl8nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl8nl1arc_arc_halt_ack
wire   i_sl8nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl8nl1arc_arc_run_ack
wire   i_sl8nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl8nl1arc_sys_sleep_r
wire   [2:0] i_sl8nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl8nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl8nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl8nl1arc_sys_halt_r
wire   i_sl8nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl8nl1arc_sys_tf_halt_r
wire   i_sl9nl1arc_arc_halt_ack;         // npu_top > arcsync_top -- npu_top.sl9nl1arc_arc_halt_ack
wire   i_sl9nl1arc_arc_run_ack;          // npu_top > arcsync_top -- npu_top.sl9nl1arc_arc_run_ack
wire   i_sl9nl1arc_sys_sleep_r;          // npu_top > arcsync_top -- npu_top.sl9nl1arc_sys_sleep_r
wire   [2:0] i_sl9nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl9nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl9nl1arc_sys_halt_r;           // npu_top > arcsync_top -- npu_top.sl9nl1arc_sys_halt_r
wire   i_sl9nl1arc_sys_tf_halt_r;        // npu_top > arcsync_top -- npu_top.sl9nl1arc_sys_tf_halt_r
wire   i_sl10nl1arc_arc_halt_ack;        // npu_top > arcsync_top -- npu_top.sl10nl1arc_arc_halt_ack
wire   i_sl10nl1arc_arc_run_ack;         // npu_top > arcsync_top -- npu_top.sl10nl1arc_arc_run_ack
wire   i_sl10nl1arc_sys_sleep_r;         // npu_top > arcsync_top -- npu_top.sl10nl1arc_sys_sleep_r
wire   [2:0] i_sl10nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl10nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl10nl1arc_sys_halt_r;          // npu_top > arcsync_top -- npu_top.sl10nl1arc_sys_halt_r
wire   i_sl10nl1arc_sys_tf_halt_r;       // npu_top > arcsync_top -- npu_top.sl10nl1arc_sys_tf_halt_r
wire   i_sl11nl1arc_arc_halt_ack;        // npu_top > arcsync_top -- npu_top.sl11nl1arc_arc_halt_ack
wire   i_sl11nl1arc_arc_run_ack;         // npu_top > arcsync_top -- npu_top.sl11nl1arc_arc_run_ack
wire   i_sl11nl1arc_sys_sleep_r;         // npu_top > arcsync_top -- npu_top.sl11nl1arc_sys_sleep_r
wire   [2:0] i_sl11nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl11nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl11nl1arc_sys_halt_r;          // npu_top > arcsync_top -- npu_top.sl11nl1arc_sys_halt_r
wire   i_sl11nl1arc_sys_tf_halt_r;       // npu_top > arcsync_top -- npu_top.sl11nl1arc_sys_tf_halt_r
wire   i_sl12nl1arc_arc_halt_ack;        // npu_top > arcsync_top -- npu_top.sl12nl1arc_arc_halt_ack
wire   i_sl12nl1arc_arc_run_ack;         // npu_top > arcsync_top -- npu_top.sl12nl1arc_arc_run_ack
wire   i_sl12nl1arc_sys_sleep_r;         // npu_top > arcsync_top -- npu_top.sl12nl1arc_sys_sleep_r
wire   [2:0] i_sl12nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl12nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl12nl1arc_sys_halt_r;          // npu_top > arcsync_top -- npu_top.sl12nl1arc_sys_halt_r
wire   i_sl12nl1arc_sys_tf_halt_r;       // npu_top > arcsync_top -- npu_top.sl12nl1arc_sys_tf_halt_r
wire   i_sl13nl1arc_arc_halt_ack;        // npu_top > arcsync_top -- npu_top.sl13nl1arc_arc_halt_ack
wire   i_sl13nl1arc_arc_run_ack;         // npu_top > arcsync_top -- npu_top.sl13nl1arc_arc_run_ack
wire   i_sl13nl1arc_sys_sleep_r;         // npu_top > arcsync_top -- npu_top.sl13nl1arc_sys_sleep_r
wire   [2:0] i_sl13nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl13nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl13nl1arc_sys_halt_r;          // npu_top > arcsync_top -- npu_top.sl13nl1arc_sys_halt_r
wire   i_sl13nl1arc_sys_tf_halt_r;       // npu_top > arcsync_top -- npu_top.sl13nl1arc_sys_tf_halt_r
wire   i_sl14nl1arc_arc_halt_ack;        // npu_top > arcsync_top -- npu_top.sl14nl1arc_arc_halt_ack
wire   i_sl14nl1arc_arc_run_ack;         // npu_top > arcsync_top -- npu_top.sl14nl1arc_arc_run_ack
wire   i_sl14nl1arc_sys_sleep_r;         // npu_top > arcsync_top -- npu_top.sl14nl1arc_sys_sleep_r
wire   [2:0] i_sl14nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl14nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl14nl1arc_sys_halt_r;          // npu_top > arcsync_top -- npu_top.sl14nl1arc_sys_halt_r
wire   i_sl14nl1arc_sys_tf_halt_r;       // npu_top > arcsync_top -- npu_top.sl14nl1arc_sys_tf_halt_r
wire   i_sl15nl1arc_arc_halt_ack;        // npu_top > arcsync_top -- npu_top.sl15nl1arc_arc_halt_ack
wire   i_sl15nl1arc_arc_run_ack;         // npu_top > arcsync_top -- npu_top.sl15nl1arc_arc_run_ack
wire   i_sl15nl1arc_sys_sleep_r;         // npu_top > arcsync_top -- npu_top.sl15nl1arc_sys_sleep_r
wire   [2:0] i_sl15nl1arc_sys_sleep_mode_r; // npu_top > arcsync_top -- npu_top.sl15nl1arc_sys_sleep_mode_r [2:0]
wire   i_sl15nl1arc_sys_halt_r;          // npu_top > arcsync_top -- npu_top.sl15nl1arc_sys_halt_r
wire   i_sl15nl1arc_sys_tf_halt_r;       // npu_top > arcsync_top -- npu_top.sl15nl1arc_sys_tf_halt_r
wire   i_nl2arc0_wdt_reset_error;        // npu_top > unconnected -- npu_top.nl2arc0_wdt_reset_error
wire   i_nl2arc0_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.nl2arc0_wdt_reset_wdt_clk_error
wire   i_nl2arc1_wdt_reset_error;        // npu_top > unconnected -- npu_top.nl2arc1_wdt_reset_error
wire   i_nl2arc1_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.nl2arc1_wdt_reset_wdt_clk_error
wire   i_sl0nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl0nl1arc_wdt_reset_error
wire   i_sl0nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl0nl1arc_wdt_reset_wdt_clk_error
wire   i_sl1nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl1nl1arc_wdt_reset_error
wire   i_sl1nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl1nl1arc_wdt_reset_wdt_clk_error
wire   i_sl2nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl2nl1arc_wdt_reset_error
wire   i_sl2nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl2nl1arc_wdt_reset_wdt_clk_error
wire   i_sl3nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl3nl1arc_wdt_reset_error
wire   i_sl3nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl3nl1arc_wdt_reset_wdt_clk_error
wire   i_sl4nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl4nl1arc_wdt_reset_error
wire   i_sl4nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl4nl1arc_wdt_reset_wdt_clk_error
wire   i_sl5nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl5nl1arc_wdt_reset_error
wire   i_sl5nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl5nl1arc_wdt_reset_wdt_clk_error
wire   i_sl6nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl6nl1arc_wdt_reset_error
wire   i_sl6nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl6nl1arc_wdt_reset_wdt_clk_error
wire   i_sl7nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl7nl1arc_wdt_reset_error
wire   i_sl7nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl7nl1arc_wdt_reset_wdt_clk_error
wire   i_sl8nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl8nl1arc_wdt_reset_error
wire   i_sl8nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl8nl1arc_wdt_reset_wdt_clk_error
wire   i_sl9nl1arc_wdt_reset_error;      // npu_top > unconnected -- npu_top.sl9nl1arc_wdt_reset_error
wire   i_sl9nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl9nl1arc_wdt_reset_wdt_clk_error
wire   i_sl10nl1arc_wdt_reset_error;     // npu_top > unconnected -- npu_top.sl10nl1arc_wdt_reset_error
wire   i_sl10nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl10nl1arc_wdt_reset_wdt_clk_error
wire   i_sl11nl1arc_wdt_reset_error;     // npu_top > unconnected -- npu_top.sl11nl1arc_wdt_reset_error
wire   i_sl11nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl11nl1arc_wdt_reset_wdt_clk_error
wire   i_sl12nl1arc_wdt_reset_error;     // npu_top > unconnected -- npu_top.sl12nl1arc_wdt_reset_error
wire   i_sl12nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl12nl1arc_wdt_reset_wdt_clk_error
wire   i_sl13nl1arc_wdt_reset_error;     // npu_top > unconnected -- npu_top.sl13nl1arc_wdt_reset_error
wire   i_sl13nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl13nl1arc_wdt_reset_wdt_clk_error
wire   i_sl14nl1arc_wdt_reset_error;     // npu_top > unconnected -- npu_top.sl14nl1arc_wdt_reset_error
wire   i_sl14nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl14nl1arc_wdt_reset_wdt_clk_error
wire   i_sl15nl1arc_wdt_reset_error;     // npu_top > unconnected -- npu_top.sl15nl1arc_wdt_reset_error
wire   i_sl15nl1arc_wdt_reset_wdt_clk_error; // npu_top > unconnected -- npu_top.sl15nl1arc_wdt_reset_wdt_clk_error
wire   i_v0c0_pwr_dwn;                   // arcsync_top > unconnected -- arcsync_top.v0c0_pwr_dwn
wire   i_v0c1_pwr_dwn;                   // arcsync_top > unconnected -- arcsync_top.v0c1_pwr_dwn
wire   i_v0c2_pwr_dwn;                   // arcsync_top > unconnected -- arcsync_top.v0c2_pwr_dwn
wire   i_v0c3_pwr_dwn;                   // arcsync_top > unconnected -- arcsync_top.v0c3_pwr_dwn

// Instantiation of module npu_top
npu_top inpu_top(
    .npu_core_clk                       (npu_core_clk) // <   outside-of-hierarchy
  , .npu_core_rst_a                     (npu_core_rst_a) // <   outside-of-hierarchy
  , .npu_noc_clk                        (npu_noc_clk) // <   outside-of-hierarchy
  , .npu_noc_rst_a                      (npu_noc_rst_a) // <   outside-of-hierarchy
  , .npu_cfg_clk                        (npu_cfg_clk) // <   outside-of-hierarchy
  , .npu_cfg_rst_a                      (npu_cfg_rst_a) // <   outside-of-hierarchy
  , .nl2arc0_wdt_clk                    (nl2arc0_wdt_clk) // <   outside-of-hierarchy
  , .nl2arc1_wdt_clk                    (nl2arc1_wdt_clk) // <   outside-of-hierarchy
  , .npu_csm_base                       (npu_csm_base) // <   outside-of-hierarchy
  , .grp0_rst_a                         (i_grp0_rst_a) // <   arcsync_top
  , .grp0_clk_en_a                      (i_grp0_clk_en) // <   arcsync_top
  , .grp1_rst_a                         (i_grp1_rst_a) // <   arcsync_top
  , .grp1_clk_en_a                      (i_grp1_clk_en) // <   arcsync_top
  , .grp2_rst_a                         (i_grp2_rst_a) // <   arcsync_top
  , .grp2_clk_en_a                      (i_grp2_clk_en) // <   arcsync_top
  , .grp3_rst_a                         (i_grp3_rst_a) // <   arcsync_top
  , .grp3_clk_en_a                      (i_grp3_clk_en) // <   arcsync_top
  , .sl0_clk                            (sl0_clk)  // <   outside-of-hierarchy
  , .sl0_wdt_clk                        (sl0_wdt_clk) // <   outside-of-hierarchy
  , .sl0_rst_a                          (i_sl0_rst_a) // <   arcsync_top
  , .sl0_clk_en_a                       (i_sl0_clk_en_a) // <   arcsync_top
  , .sl1_clk                            (sl1_clk)  // <   outside-of-hierarchy
  , .sl1_wdt_clk                        (sl1_wdt_clk) // <   outside-of-hierarchy
  , .sl1_rst_a                          (i_sl1_rst_a) // <   arcsync_top
  , .sl1_clk_en_a                       (i_sl1_clk_en_a) // <   arcsync_top
  , .sl2_clk                            (sl2_clk)  // <   outside-of-hierarchy
  , .sl2_wdt_clk                        (sl2_wdt_clk) // <   outside-of-hierarchy
  , .sl2_rst_a                          (i_sl2_rst_a) // <   arcsync_top
  , .sl2_clk_en_a                       (i_sl2_clk_en_a) // <   arcsync_top
  , .sl3_clk                            (sl3_clk)  // <   outside-of-hierarchy
  , .sl3_wdt_clk                        (sl3_wdt_clk) // <   outside-of-hierarchy
  , .sl3_rst_a                          (i_sl3_rst_a) // <   arcsync_top
  , .sl3_clk_en_a                       (i_sl3_clk_en_a) // <   arcsync_top
  , .sl4_clk                            (sl4_clk)  // <   outside-of-hierarchy
  , .sl4_wdt_clk                        (sl4_wdt_clk) // <   outside-of-hierarchy
  , .sl4_rst_a                          (i_sl4_rst_a) // <   arcsync_top
  , .sl4_clk_en_a                       (i_sl4_clk_en_a) // <   arcsync_top
  , .sl5_clk                            (sl5_clk)  // <   outside-of-hierarchy
  , .sl5_wdt_clk                        (sl5_wdt_clk) // <   outside-of-hierarchy
  , .sl5_rst_a                          (i_sl5_rst_a) // <   arcsync_top
  , .sl5_clk_en_a                       (i_sl5_clk_en_a) // <   arcsync_top
  , .sl6_clk                            (sl6_clk)  // <   outside-of-hierarchy
  , .sl6_wdt_clk                        (sl6_wdt_clk) // <   outside-of-hierarchy
  , .sl6_rst_a                          (i_sl6_rst_a) // <   arcsync_top
  , .sl6_clk_en_a                       (i_sl6_clk_en_a) // <   arcsync_top
  , .sl7_clk                            (sl7_clk)  // <   outside-of-hierarchy
  , .sl7_wdt_clk                        (sl7_wdt_clk) // <   outside-of-hierarchy
  , .sl7_rst_a                          (i_sl7_rst_a) // <   arcsync_top
  , .sl7_clk_en_a                       (i_sl7_clk_en_a) // <   arcsync_top
  , .sl8_clk                            (sl8_clk)  // <   outside-of-hierarchy
  , .sl8_wdt_clk                        (sl8_wdt_clk) // <   outside-of-hierarchy
  , .sl8_rst_a                          (i_sl8_rst_a) // <   arcsync_top
  , .sl8_clk_en_a                       (i_sl8_clk_en_a) // <   arcsync_top
  , .sl9_clk                            (sl9_clk)  // <   outside-of-hierarchy
  , .sl9_wdt_clk                        (sl9_wdt_clk) // <   outside-of-hierarchy
  , .sl9_rst_a                          (i_sl9_rst_a) // <   arcsync_top
  , .sl9_clk_en_a                       (i_sl9_clk_en_a) // <   arcsync_top
  , .sl10_clk                           (sl10_clk) // <   outside-of-hierarchy
  , .sl10_wdt_clk                       (sl10_wdt_clk) // <   outside-of-hierarchy
  , .sl10_rst_a                         (i_sl10_rst_a) // <   arcsync_top
  , .sl10_clk_en_a                      (i_sl10_clk_en_a) // <   arcsync_top
  , .sl11_clk                           (sl11_clk) // <   outside-of-hierarchy
  , .sl11_wdt_clk                       (sl11_wdt_clk) // <   outside-of-hierarchy
  , .sl11_rst_a                         (i_sl11_rst_a) // <   arcsync_top
  , .sl11_clk_en_a                      (i_sl11_clk_en_a) // <   arcsync_top
  , .sl12_clk                           (sl12_clk) // <   outside-of-hierarchy
  , .sl12_wdt_clk                       (sl12_wdt_clk) // <   outside-of-hierarchy
  , .sl12_rst_a                         (i_sl12_rst_a) // <   arcsync_top
  , .sl12_clk_en_a                      (i_sl12_clk_en_a) // <   arcsync_top
  , .sl13_clk                           (sl13_clk) // <   outside-of-hierarchy
  , .sl13_wdt_clk                       (sl13_wdt_clk) // <   outside-of-hierarchy
  , .sl13_rst_a                         (i_sl13_rst_a) // <   arcsync_top
  , .sl13_clk_en_a                      (i_sl13_clk_en_a) // <   arcsync_top
  , .sl14_clk                           (sl14_clk) // <   outside-of-hierarchy
  , .sl14_wdt_clk                       (sl14_wdt_clk) // <   outside-of-hierarchy
  , .sl14_rst_a                         (i_sl14_rst_a) // <   arcsync_top
  , .sl14_clk_en_a                      (i_sl14_clk_en_a) // <   arcsync_top
  , .sl15_clk                           (sl15_clk) // <   outside-of-hierarchy
  , .sl15_wdt_clk                       (sl15_wdt_clk) // <   outside-of-hierarchy
  , .sl15_rst_a                         (i_sl15_rst_a) // <   arcsync_top
  , .sl15_clk_en_a                      (i_sl15_clk_en_a) // <   arcsync_top
  , .nl2arc0_rst_a                      (i_nl2arc0_rst_a) // <   arcsync_top
  , .nl2arc0_clk_en_a                   (i_nl2arc0_clk_en_a) // <   arcsync_top
  , .nl2arc1_rst_a                      (i_nl2arc1_rst_a) // <   arcsync_top
  , .nl2arc1_clk_en_a                   (i_nl2arc1_clk_en_a) // <   arcsync_top
  , .nl2_rst_a                          (i_nl2_rst_a) // <   arcsync_top
  , .npu_mst0_axi_arready               (npu_mst0_axi_arready) // <   alb_mss_fab
  , .npu_mst0_axi_rvalid                (npu_mst0_axi_rvalid) // <   alb_mss_fab
  , .npu_mst0_axi_rid                   (npu_mst0_axi_rid) // <   alb_mss_fab
  , .npu_mst0_axi_rdata                 (npu_mst0_axi_rdata) // <   alb_mss_fab
  , .npu_mst0_axi_rresp                 (npu_mst0_axi_rresp) // <   alb_mss_fab
  , .npu_mst0_axi_rlast                 (npu_mst0_axi_rlast) // <   alb_mss_fab
  , .npu_mst0_axi_awready               (npu_mst0_axi_awready) // <   alb_mss_fab
  , .npu_mst0_axi_wready                (npu_mst0_axi_wready) // <   alb_mss_fab
  , .npu_mst0_axi_bvalid                (npu_mst0_axi_bvalid) // <   alb_mss_fab
  , .npu_mst0_axi_bid                   (npu_mst0_axi_bid) // <   alb_mss_fab
  , .npu_mst0_axi_bresp                 (npu_mst0_axi_bresp) // <   alb_mss_fab
  , .npu_mst1_axi_arready               (npu_mst1_axi_arready) // <   alb_mss_fab
  , .npu_mst1_axi_rvalid                (npu_mst1_axi_rvalid) // <   alb_mss_fab
  , .npu_mst1_axi_rid                   (npu_mst1_axi_rid) // <   alb_mss_fab
  , .npu_mst1_axi_rdata                 (npu_mst1_axi_rdata) // <   alb_mss_fab
  , .npu_mst1_axi_rresp                 (npu_mst1_axi_rresp) // <   alb_mss_fab
  , .npu_mst1_axi_rlast                 (npu_mst1_axi_rlast) // <   alb_mss_fab
  , .npu_mst1_axi_awready               (npu_mst1_axi_awready) // <   alb_mss_fab
  , .npu_mst1_axi_wready                (npu_mst1_axi_wready) // <   alb_mss_fab
  , .npu_mst1_axi_bvalid                (npu_mst1_axi_bvalid) // <   alb_mss_fab
  , .npu_mst1_axi_bid                   (npu_mst1_axi_bid) // <   alb_mss_fab
  , .npu_mst1_axi_bresp                 (npu_mst1_axi_bresp) // <   alb_mss_fab
  , .npu_mst2_axi_arready               (npu_mst2_axi_arready) // <   alb_mss_fab
  , .npu_mst2_axi_rvalid                (npu_mst2_axi_rvalid) // <   alb_mss_fab
  , .npu_mst2_axi_rid                   (npu_mst2_axi_rid) // <   alb_mss_fab
  , .npu_mst2_axi_rdata                 (npu_mst2_axi_rdata) // <   alb_mss_fab
  , .npu_mst2_axi_rresp                 (npu_mst2_axi_rresp) // <   alb_mss_fab
  , .npu_mst2_axi_rlast                 (npu_mst2_axi_rlast) // <   alb_mss_fab
  , .npu_mst2_axi_awready               (npu_mst2_axi_awready) // <   alb_mss_fab
  , .npu_mst2_axi_wready                (npu_mst2_axi_wready) // <   alb_mss_fab
  , .npu_mst2_axi_bvalid                (npu_mst2_axi_bvalid) // <   alb_mss_fab
  , .npu_mst2_axi_bid                   (npu_mst2_axi_bid) // <   alb_mss_fab
  , .npu_mst2_axi_bresp                 (npu_mst2_axi_bresp) // <   alb_mss_fab
  , .npu_mst3_axi_arready               (npu_mst3_axi_arready) // <   alb_mss_fab
  , .npu_mst3_axi_rvalid                (npu_mst3_axi_rvalid) // <   alb_mss_fab
  , .npu_mst3_axi_rid                   (npu_mst3_axi_rid) // <   alb_mss_fab
  , .npu_mst3_axi_rdata                 (npu_mst3_axi_rdata) // <   alb_mss_fab
  , .npu_mst3_axi_rresp                 (npu_mst3_axi_rresp) // <   alb_mss_fab
  , .npu_mst3_axi_rlast                 (npu_mst3_axi_rlast) // <   alb_mss_fab
  , .npu_mst3_axi_awready               (npu_mst3_axi_awready) // <   alb_mss_fab
  , .npu_mst3_axi_wready                (npu_mst3_axi_wready) // <   alb_mss_fab
  , .npu_mst3_axi_bvalid                (npu_mst3_axi_bvalid) // <   alb_mss_fab
  , .npu_mst3_axi_bid                   (npu_mst3_axi_bid) // <   alb_mss_fab
  , .npu_mst3_axi_bresp                 (npu_mst3_axi_bresp) // <   alb_mss_fab
  , .npu_mst4_axi_arready               (npu_mst4_axi_arready) // <   alb_mss_fab
  , .npu_mst4_axi_rvalid                (npu_mst4_axi_rvalid) // <   alb_mss_fab
  , .npu_mst4_axi_rid                   (npu_mst4_axi_rid) // <   alb_mss_fab
  , .npu_mst4_axi_rdata                 (npu_mst4_axi_rdata) // <   alb_mss_fab
  , .npu_mst4_axi_rresp                 (npu_mst4_axi_rresp) // <   alb_mss_fab
  , .npu_mst4_axi_rlast                 (npu_mst4_axi_rlast) // <   alb_mss_fab
  , .npu_mst4_axi_awready               (npu_mst4_axi_awready) // <   alb_mss_fab
  , .npu_mst4_axi_wready                (npu_mst4_axi_wready) // <   alb_mss_fab
  , .npu_mst4_axi_bvalid                (npu_mst4_axi_bvalid) // <   alb_mss_fab
  , .npu_mst4_axi_bid                   (npu_mst4_axi_bid) // <   alb_mss_fab
  , .npu_mst4_axi_bresp                 (npu_mst4_axi_bresp) // <   alb_mss_fab
  , .npu_dmi0_axi_arvalid               (npu_dmi0_axi_arvalid) // <   alb_mss_fab
  , .npu_dmi0_axi_arid                  (npu_dmi0_axi_arid) // <   alb_mss_fab
  , .npu_dmi0_axi_araddr                (npu_dmi0_axi_araddr) // <   alb_mss_fab
  , .npu_dmi0_axi_arcache               (npu_dmi0_axi_arcache) // <   alb_mss_fab
  , .npu_dmi0_axi_arprot                (npu_dmi0_axi_arprot) // <   alb_mss_fab
  , .npu_dmi0_axi_arlock                (npu_dmi0_axi_arlock) // <   alb_mss_fab
  , .npu_dmi0_axi_arburst               (npu_dmi0_axi_arburst) // <   alb_mss_fab
  , .npu_dmi0_axi_arlen                 (npu_dmi0_axi_arlen) // <   alb_mss_fab
  , .npu_dmi0_axi_arsize                (npu_dmi0_axi_arsize) // <   alb_mss_fab
  , .npu_dmi0_axi_rready                (npu_dmi0_axi_rready) // <   alb_mss_fab
  , .npu_dmi0_axi_awvalid               (npu_dmi0_axi_awvalid) // <   alb_mss_fab
  , .npu_dmi0_axi_awid                  (npu_dmi0_axi_awid) // <   alb_mss_fab
  , .npu_dmi0_axi_awaddr                (npu_dmi0_axi_awaddr) // <   alb_mss_fab
  , .npu_dmi0_axi_awcache               (npu_dmi0_axi_awcache) // <   alb_mss_fab
  , .npu_dmi0_axi_awprot                (npu_dmi0_axi_awprot) // <   alb_mss_fab
  , .npu_dmi0_axi_awlock                (npu_dmi0_axi_awlock) // <   alb_mss_fab
  , .npu_dmi0_axi_awburst               (npu_dmi0_axi_awburst) // <   alb_mss_fab
  , .npu_dmi0_axi_awlen                 (npu_dmi0_axi_awlen) // <   alb_mss_fab
  , .npu_dmi0_axi_awsize                (npu_dmi0_axi_awsize) // <   alb_mss_fab
  , .npu_dmi0_axi_wvalid                (npu_dmi0_axi_wvalid) // <   alb_mss_fab
  , .npu_dmi0_axi_wdata                 (npu_dmi0_axi_wdata) // <   alb_mss_fab
  , .npu_dmi0_axi_wstrb                 (npu_dmi0_axi_wstrb) // <   alb_mss_fab
  , .npu_dmi0_axi_wlast                 (npu_dmi0_axi_wlast) // <   alb_mss_fab
  , .npu_dmi0_axi_bready                (npu_dmi0_axi_bready) // <   alb_mss_fab
  , .npu_cfg_axi_arvalid                (npu_cfg_axi_arvalid) // <   alb_mss_fab
  , .npu_cfg_axi_arid                   (npu_cfg_axi_arid) // <   alb_mss_fab
  , .npu_cfg_axi_araddr                 (npu_cfg_axi_araddr) // <   alb_mss_fab
  , .npu_cfg_axi_arcache                (npu_cfg_axi_arcache) // <   alb_mss_fab
  , .npu_cfg_axi_arprot                 (npu_cfg_axi_arprot) // <   alb_mss_fab
  , .npu_cfg_axi_arlock                 (npu_cfg_axi_arlock) // <   alb_mss_fab
  , .npu_cfg_axi_arburst                (npu_cfg_axi_arburst) // <   alb_mss_fab
  , .npu_cfg_axi_arlen                  (npu_cfg_axi_arlen) // <   alb_mss_fab
  , .npu_cfg_axi_arsize                 (npu_cfg_axi_arsize) // <   alb_mss_fab
  , .npu_cfg_axi_rready                 (npu_cfg_axi_rready) // <   alb_mss_fab
  , .npu_cfg_axi_awvalid                (npu_cfg_axi_awvalid) // <   alb_mss_fab
  , .npu_cfg_axi_awid                   (npu_cfg_axi_awid) // <   alb_mss_fab
  , .npu_cfg_axi_awaddr                 (npu_cfg_axi_awaddr) // <   alb_mss_fab
  , .npu_cfg_axi_awcache                (npu_cfg_axi_awcache) // <   alb_mss_fab
  , .npu_cfg_axi_awprot                 (npu_cfg_axi_awprot) // <   alb_mss_fab
  , .npu_cfg_axi_awlock                 (npu_cfg_axi_awlock) // <   alb_mss_fab
  , .npu_cfg_axi_awburst                (npu_cfg_axi_awburst) // <   alb_mss_fab
  , .npu_cfg_axi_awlen                  (npu_cfg_axi_awlen) // <   alb_mss_fab
  , .npu_cfg_axi_awsize                 (npu_cfg_axi_awsize) // <   alb_mss_fab
  , .npu_cfg_axi_wvalid                 (npu_cfg_axi_wvalid) // <   alb_mss_fab
  , .npu_cfg_axi_wdata                  (npu_cfg_axi_wdata) // <   alb_mss_fab
  , .npu_cfg_axi_wstrb                  (npu_cfg_axi_wstrb) // <   alb_mss_fab
  , .npu_cfg_axi_wlast                  (npu_cfg_axi_wlast) // <   alb_mss_fab
  , .npu_cfg_axi_bready                 (npu_cfg_axi_bready) // <   alb_mss_fab
  , .nl2arc_pwr_dwn_a                   (i_nl2arc_pwr_dwn) // <   arcsync_top
  , .nl2arc0_pwr_dwn_a                  (i_nl2arc0_pwr_dwn) // <   arcsync_top
  , .nl2arc1_pwr_dwn_a                  (i_nl2arc1_pwr_dwn) // <   arcsync_top
  , .grp0_pwr_dwn_a                     (i_grp0_pwr_dwn) // <   arcsync_top
  , .grp1_pwr_dwn_a                     (i_grp1_pwr_dwn) // <   arcsync_top
  , .grp2_pwr_dwn_a                     (i_grp2_pwr_dwn) // <   arcsync_top
  , .grp3_pwr_dwn_a                     (i_grp3_pwr_dwn) // <   arcsync_top
  , .sl0nl1arc_pwr_dwn_a                (i_sl0nl1arc_pwr_dwn) // <   arcsync_top
  , .sl1nl1arc_pwr_dwn_a                (i_sl1nl1arc_pwr_dwn) // <   arcsync_top
  , .sl2nl1arc_pwr_dwn_a                (i_sl2nl1arc_pwr_dwn) // <   arcsync_top
  , .sl3nl1arc_pwr_dwn_a                (i_sl3nl1arc_pwr_dwn) // <   arcsync_top
  , .sl4nl1arc_pwr_dwn_a                (i_sl4nl1arc_pwr_dwn) // <   arcsync_top
  , .sl5nl1arc_pwr_dwn_a                (i_sl5nl1arc_pwr_dwn) // <   arcsync_top
  , .sl6nl1arc_pwr_dwn_a                (i_sl6nl1arc_pwr_dwn) // <   arcsync_top
  , .sl7nl1arc_pwr_dwn_a                (i_sl7nl1arc_pwr_dwn) // <   arcsync_top
  , .sl8nl1arc_pwr_dwn_a                (i_sl8nl1arc_pwr_dwn) // <   arcsync_top
  , .sl9nl1arc_pwr_dwn_a                (i_sl9nl1arc_pwr_dwn) // <   arcsync_top
  , .sl10nl1arc_pwr_dwn_a               (i_sl10nl1arc_pwr_dwn) // <   arcsync_top
  , .sl11nl1arc_pwr_dwn_a               (i_sl11nl1arc_pwr_dwn) // <   arcsync_top
  , .sl12nl1arc_pwr_dwn_a               (i_sl12nl1arc_pwr_dwn) // <   arcsync_top
  , .sl13nl1arc_pwr_dwn_a               (i_sl13nl1arc_pwr_dwn) // <   arcsync_top
  , .sl14nl1arc_pwr_dwn_a               (i_sl14nl1arc_pwr_dwn) // <   arcsync_top
  , .sl15nl1arc_pwr_dwn_a               (i_sl15nl1arc_pwr_dwn) // <   arcsync_top
  , .nl2arc_isolate_n                   (i_nl2arc_isolate_n) // <   arcsync_top
  , .nl2arc_isolate                     (i_nl2arc_isolate) // <   arcsync_top
  , .nl2arc_pd_mem                      (i_nl2arc_pd_mem) // <   arcsync_top
  , .nl2arc_pd_logic                    (i_nl2arc_pd_logic) // <   arcsync_top
  , .grp0_isolate_n                     (i_grp0_isolate_n) // <   arcsync_top
  , .grp0_isolate                       (i_grp0_isolate) // <   arcsync_top
  , .grp0_pd_mem                        (i_grp0_pd_mem) // <   arcsync_top
  , .grp0_pd_logic                      (i_grp0_pd_logic) // <   arcsync_top
  , .grp1_isolate_n                     (i_grp1_isolate_n) // <   arcsync_top
  , .grp1_isolate                       (i_grp1_isolate) // <   arcsync_top
  , .grp1_pd_mem                        (i_grp1_pd_mem) // <   arcsync_top
  , .grp1_pd_logic                      (i_grp1_pd_logic) // <   arcsync_top
  , .grp2_isolate_n                     (i_grp2_isolate_n) // <   arcsync_top
  , .grp2_isolate                       (i_grp2_isolate) // <   arcsync_top
  , .grp2_pd_mem                        (i_grp2_pd_mem) // <   arcsync_top
  , .grp2_pd_logic                      (i_grp2_pd_logic) // <   arcsync_top
  , .grp3_isolate_n                     (i_grp3_isolate_n) // <   arcsync_top
  , .grp3_isolate                       (i_grp3_isolate) // <   arcsync_top
  , .grp3_pd_mem                        (i_grp3_pd_mem) // <   arcsync_top
  , .grp3_pd_logic                      (i_grp3_pd_logic) // <   arcsync_top
  , .sl0nl1arc_isolate_n                (i_sl0nl1arc_isolate_n) // <   arcsync_top
  , .sl0nl1arc_isolate                  (i_sl0nl1arc_isolate) // <   arcsync_top
  , .sl0nl1arc_pd_mem                   (i_sl0nl1arc_pd_mem) // <   arcsync_top
  , .sl0nl1arc_pd_logic                 (i_sl0nl1arc_pd_logic) // <   arcsync_top
  , .sl1nl1arc_isolate_n                (i_sl1nl1arc_isolate_n) // <   arcsync_top
  , .sl1nl1arc_isolate                  (i_sl1nl1arc_isolate) // <   arcsync_top
  , .sl1nl1arc_pd_mem                   (i_sl1nl1arc_pd_mem) // <   arcsync_top
  , .sl1nl1arc_pd_logic                 (i_sl1nl1arc_pd_logic) // <   arcsync_top
  , .sl2nl1arc_isolate_n                (i_sl2nl1arc_isolate_n) // <   arcsync_top
  , .sl2nl1arc_isolate                  (i_sl2nl1arc_isolate) // <   arcsync_top
  , .sl2nl1arc_pd_mem                   (i_sl2nl1arc_pd_mem) // <   arcsync_top
  , .sl2nl1arc_pd_logic                 (i_sl2nl1arc_pd_logic) // <   arcsync_top
  , .sl3nl1arc_isolate_n                (i_sl3nl1arc_isolate_n) // <   arcsync_top
  , .sl3nl1arc_isolate                  (i_sl3nl1arc_isolate) // <   arcsync_top
  , .sl3nl1arc_pd_mem                   (i_sl3nl1arc_pd_mem) // <   arcsync_top
  , .sl3nl1arc_pd_logic                 (i_sl3nl1arc_pd_logic) // <   arcsync_top
  , .sl4nl1arc_isolate_n                (i_sl4nl1arc_isolate_n) // <   arcsync_top
  , .sl4nl1arc_isolate                  (i_sl4nl1arc_isolate) // <   arcsync_top
  , .sl4nl1arc_pd_mem                   (i_sl4nl1arc_pd_mem) // <   arcsync_top
  , .sl4nl1arc_pd_logic                 (i_sl4nl1arc_pd_logic) // <   arcsync_top
  , .sl5nl1arc_isolate_n                (i_sl5nl1arc_isolate_n) // <   arcsync_top
  , .sl5nl1arc_isolate                  (i_sl5nl1arc_isolate) // <   arcsync_top
  , .sl5nl1arc_pd_mem                   (i_sl5nl1arc_pd_mem) // <   arcsync_top
  , .sl5nl1arc_pd_logic                 (i_sl5nl1arc_pd_logic) // <   arcsync_top
  , .sl6nl1arc_isolate_n                (i_sl6nl1arc_isolate_n) // <   arcsync_top
  , .sl6nl1arc_isolate                  (i_sl6nl1arc_isolate) // <   arcsync_top
  , .sl6nl1arc_pd_mem                   (i_sl6nl1arc_pd_mem) // <   arcsync_top
  , .sl6nl1arc_pd_logic                 (i_sl6nl1arc_pd_logic) // <   arcsync_top
  , .sl7nl1arc_isolate_n                (i_sl7nl1arc_isolate_n) // <   arcsync_top
  , .sl7nl1arc_isolate                  (i_sl7nl1arc_isolate) // <   arcsync_top
  , .sl7nl1arc_pd_mem                   (i_sl7nl1arc_pd_mem) // <   arcsync_top
  , .sl7nl1arc_pd_logic                 (i_sl7nl1arc_pd_logic) // <   arcsync_top
  , .sl8nl1arc_isolate_n                (i_sl8nl1arc_isolate_n) // <   arcsync_top
  , .sl8nl1arc_isolate                  (i_sl8nl1arc_isolate) // <   arcsync_top
  , .sl8nl1arc_pd_mem                   (i_sl8nl1arc_pd_mem) // <   arcsync_top
  , .sl8nl1arc_pd_logic                 (i_sl8nl1arc_pd_logic) // <   arcsync_top
  , .sl9nl1arc_isolate_n                (i_sl9nl1arc_isolate_n) // <   arcsync_top
  , .sl9nl1arc_isolate                  (i_sl9nl1arc_isolate) // <   arcsync_top
  , .sl9nl1arc_pd_mem                   (i_sl9nl1arc_pd_mem) // <   arcsync_top
  , .sl9nl1arc_pd_logic                 (i_sl9nl1arc_pd_logic) // <   arcsync_top
  , .sl10nl1arc_isolate_n               (i_sl10nl1arc_isolate_n) // <   arcsync_top
  , .sl10nl1arc_isolate                 (i_sl10nl1arc_isolate) // <   arcsync_top
  , .sl10nl1arc_pd_mem                  (i_sl10nl1arc_pd_mem) // <   arcsync_top
  , .sl10nl1arc_pd_logic                (i_sl10nl1arc_pd_logic) // <   arcsync_top
  , .sl11nl1arc_isolate_n               (i_sl11nl1arc_isolate_n) // <   arcsync_top
  , .sl11nl1arc_isolate                 (i_sl11nl1arc_isolate) // <   arcsync_top
  , .sl11nl1arc_pd_mem                  (i_sl11nl1arc_pd_mem) // <   arcsync_top
  , .sl11nl1arc_pd_logic                (i_sl11nl1arc_pd_logic) // <   arcsync_top
  , .sl12nl1arc_isolate_n               (i_sl12nl1arc_isolate_n) // <   arcsync_top
  , .sl12nl1arc_isolate                 (i_sl12nl1arc_isolate) // <   arcsync_top
  , .sl12nl1arc_pd_mem                  (i_sl12nl1arc_pd_mem) // <   arcsync_top
  , .sl12nl1arc_pd_logic                (i_sl12nl1arc_pd_logic) // <   arcsync_top
  , .sl13nl1arc_isolate_n               (i_sl13nl1arc_isolate_n) // <   arcsync_top
  , .sl13nl1arc_isolate                 (i_sl13nl1arc_isolate) // <   arcsync_top
  , .sl13nl1arc_pd_mem                  (i_sl13nl1arc_pd_mem) // <   arcsync_top
  , .sl13nl1arc_pd_logic                (i_sl13nl1arc_pd_logic) // <   arcsync_top
  , .sl14nl1arc_isolate_n               (i_sl14nl1arc_isolate_n) // <   arcsync_top
  , .sl14nl1arc_isolate                 (i_sl14nl1arc_isolate) // <   arcsync_top
  , .sl14nl1arc_pd_mem                  (i_sl14nl1arc_pd_mem) // <   arcsync_top
  , .sl14nl1arc_pd_logic                (i_sl14nl1arc_pd_logic) // <   arcsync_top
  , .sl15nl1arc_isolate_n               (i_sl15nl1arc_isolate_n) // <   arcsync_top
  , .sl15nl1arc_isolate                 (i_sl15nl1arc_isolate) // <   arcsync_top
  , .sl15nl1arc_pd_mem                  (i_sl15nl1arc_pd_mem) // <   arcsync_top
  , .sl15nl1arc_pd_logic                (i_sl15nl1arc_pd_logic) // <   arcsync_top
  , .nl2arc_irq0_a                      (nl2arc_irq0_a) // <   outside-of-hierarchy
  , .nl2arc_irq1_a                      (nl2arc_irq1_a) // <   outside-of-hierarchy
  , .nl2arc0_intvbase_in                (i_nl2arc0_intvbase_in) // <   arcsync_top
  , .nl2arc0_arc_halt_req_a             (i_nl2arc0_arc_halt_req) // <   arcsync_top
  , .nl2arc0_arc_run_req_a              (i_nl2arc0_arc_run_req) // <   arcsync_top
  , .nl2arc0_arc_irq_a                  (i_nl2arc0_arc_irq_a) // <   arcsync_top
  , .nl2arc0_arc_event_a                (i_nl2arc0_arc_event_a) // <   arcsync_top
  , .nl2arc1_intvbase_in                (i_nl2arc1_intvbase_in) // <   arcsync_top
  , .nl2arc1_arc_halt_req_a             (i_nl2arc1_arc_halt_req) // <   arcsync_top
  , .nl2arc1_arc_run_req_a              (i_nl2arc1_arc_run_req) // <   arcsync_top
  , .nl2arc1_arc_irq_a                  (i_nl2arc1_arc_irq_a) // <   arcsync_top
  , .nl2arc1_arc_event_a                (i_nl2arc1_arc_event_a) // <   arcsync_top
  , .sl0nl1arc_intvbase_in              (i_sl0nl1arc_intvbase_in) // <   arcsync_top
  , .sl0nl1arc_arc_halt_req_a           (i_sl0nl1arc_arc_halt_req) // <   arcsync_top
  , .sl0nl1arc_arc_run_req_a            (i_sl0nl1arc_arc_run_req) // <   arcsync_top
  , .sl0nl1arc_arc_irq_a                (i_sl0nl1arc_arc_irq_a) // <   arcsync_top
  , .sl1nl1arc_intvbase_in              (i_sl1nl1arc_intvbase_in) // <   arcsync_top
  , .sl1nl1arc_arc_halt_req_a           (i_sl1nl1arc_arc_halt_req) // <   arcsync_top
  , .sl1nl1arc_arc_run_req_a            (i_sl1nl1arc_arc_run_req) // <   arcsync_top
  , .sl1nl1arc_arc_irq_a                (i_sl1nl1arc_arc_irq_a) // <   arcsync_top
  , .sl2nl1arc_intvbase_in              (i_sl2nl1arc_intvbase_in) // <   arcsync_top
  , .sl2nl1arc_arc_halt_req_a           (i_sl2nl1arc_arc_halt_req) // <   arcsync_top
  , .sl2nl1arc_arc_run_req_a            (i_sl2nl1arc_arc_run_req) // <   arcsync_top
  , .sl2nl1arc_arc_irq_a                (i_sl2nl1arc_arc_irq_a) // <   arcsync_top
  , .sl3nl1arc_intvbase_in              (i_sl3nl1arc_intvbase_in) // <   arcsync_top
  , .sl3nl1arc_arc_halt_req_a           (i_sl3nl1arc_arc_halt_req) // <   arcsync_top
  , .sl3nl1arc_arc_run_req_a            (i_sl3nl1arc_arc_run_req) // <   arcsync_top
  , .sl3nl1arc_arc_irq_a                (i_sl3nl1arc_arc_irq_a) // <   arcsync_top
  , .sl4nl1arc_intvbase_in              (i_sl4nl1arc_intvbase_in) // <   arcsync_top
  , .sl4nl1arc_arc_halt_req_a           (i_sl4nl1arc_arc_halt_req) // <   arcsync_top
  , .sl4nl1arc_arc_run_req_a            (i_sl4nl1arc_arc_run_req) // <   arcsync_top
  , .sl4nl1arc_arc_irq_a                (i_sl4nl1arc_arc_irq_a) // <   arcsync_top
  , .sl5nl1arc_intvbase_in              (i_sl5nl1arc_intvbase_in) // <   arcsync_top
  , .sl5nl1arc_arc_halt_req_a           (i_sl5nl1arc_arc_halt_req) // <   arcsync_top
  , .sl5nl1arc_arc_run_req_a            (i_sl5nl1arc_arc_run_req) // <   arcsync_top
  , .sl5nl1arc_arc_irq_a                (i_sl5nl1arc_arc_irq_a) // <   arcsync_top
  , .sl6nl1arc_intvbase_in              (i_sl6nl1arc_intvbase_in) // <   arcsync_top
  , .sl6nl1arc_arc_halt_req_a           (i_sl6nl1arc_arc_halt_req) // <   arcsync_top
  , .sl6nl1arc_arc_run_req_a            (i_sl6nl1arc_arc_run_req) // <   arcsync_top
  , .sl6nl1arc_arc_irq_a                (i_sl6nl1arc_arc_irq_a) // <   arcsync_top
  , .sl7nl1arc_intvbase_in              (i_sl7nl1arc_intvbase_in) // <   arcsync_top
  , .sl7nl1arc_arc_halt_req_a           (i_sl7nl1arc_arc_halt_req) // <   arcsync_top
  , .sl7nl1arc_arc_run_req_a            (i_sl7nl1arc_arc_run_req) // <   arcsync_top
  , .sl7nl1arc_arc_irq_a                (i_sl7nl1arc_arc_irq_a) // <   arcsync_top
  , .sl8nl1arc_intvbase_in              (i_sl8nl1arc_intvbase_in) // <   arcsync_top
  , .sl8nl1arc_arc_halt_req_a           (i_sl8nl1arc_arc_halt_req) // <   arcsync_top
  , .sl8nl1arc_arc_run_req_a            (i_sl8nl1arc_arc_run_req) // <   arcsync_top
  , .sl8nl1arc_arc_irq_a                (i_sl8nl1arc_arc_irq_a) // <   arcsync_top
  , .sl9nl1arc_intvbase_in              (i_sl9nl1arc_intvbase_in) // <   arcsync_top
  , .sl9nl1arc_arc_halt_req_a           (i_sl9nl1arc_arc_halt_req) // <   arcsync_top
  , .sl9nl1arc_arc_run_req_a            (i_sl9nl1arc_arc_run_req) // <   arcsync_top
  , .sl9nl1arc_arc_irq_a                (i_sl9nl1arc_arc_irq_a) // <   arcsync_top
  , .sl10nl1arc_intvbase_in             (i_sl10nl1arc_intvbase_in) // <   arcsync_top
  , .sl10nl1arc_arc_halt_req_a          (i_sl10nl1arc_arc_halt_req) // <   arcsync_top
  , .sl10nl1arc_arc_run_req_a           (i_sl10nl1arc_arc_run_req) // <   arcsync_top
  , .sl10nl1arc_arc_irq_a               (i_sl10nl1arc_arc_irq_a) // <   arcsync_top
  , .sl11nl1arc_intvbase_in             (i_sl11nl1arc_intvbase_in) // <   arcsync_top
  , .sl11nl1arc_arc_halt_req_a          (i_sl11nl1arc_arc_halt_req) // <   arcsync_top
  , .sl11nl1arc_arc_run_req_a           (i_sl11nl1arc_arc_run_req) // <   arcsync_top
  , .sl11nl1arc_arc_irq_a               (i_sl11nl1arc_arc_irq_a) // <   arcsync_top
  , .sl12nl1arc_intvbase_in             (i_sl12nl1arc_intvbase_in) // <   arcsync_top
  , .sl12nl1arc_arc_halt_req_a          (i_sl12nl1arc_arc_halt_req) // <   arcsync_top
  , .sl12nl1arc_arc_run_req_a           (i_sl12nl1arc_arc_run_req) // <   arcsync_top
  , .sl12nl1arc_arc_irq_a               (i_sl12nl1arc_arc_irq_a) // <   arcsync_top
  , .sl13nl1arc_intvbase_in             (i_sl13nl1arc_intvbase_in) // <   arcsync_top
  , .sl13nl1arc_arc_halt_req_a          (i_sl13nl1arc_arc_halt_req) // <   arcsync_top
  , .sl13nl1arc_arc_run_req_a           (i_sl13nl1arc_arc_run_req) // <   arcsync_top
  , .sl13nl1arc_arc_irq_a               (i_sl13nl1arc_arc_irq_a) // <   arcsync_top
  , .sl14nl1arc_intvbase_in             (i_sl14nl1arc_intvbase_in) // <   arcsync_top
  , .sl14nl1arc_arc_halt_req_a          (i_sl14nl1arc_arc_halt_req) // <   arcsync_top
  , .sl14nl1arc_arc_run_req_a           (i_sl14nl1arc_arc_run_req) // <   arcsync_top
  , .sl14nl1arc_arc_irq_a               (i_sl14nl1arc_arc_irq_a) // <   arcsync_top
  , .sl15nl1arc_intvbase_in             (i_sl15nl1arc_intvbase_in) // <   arcsync_top
  , .sl15nl1arc_arc_halt_req_a          (i_sl15nl1arc_arc_halt_req) // <   arcsync_top
  , .sl15nl1arc_arc_run_req_a           (i_sl15nl1arc_arc_run_req) // <   arcsync_top
  , .sl15nl1arc_arc_irq_a               (i_sl15nl1arc_arc_irq_a) // <   arcsync_top
  , .atclken                            (atclken)  // <   outside-of-hierarchy
  , .atresetn                           (atresetn) // <   outside-of-hierarchy
  , .atb_cstimestamp                    (atb_cstimestamp) // <   outside-of-hierarchy
  , .atready                            (atready)  // <   outside-of-hierarchy
  , .afvalid                            (afvalid)  // <   outside-of-hierarchy
  , .syncreq                            (syncreq)  // <   outside-of-hierarchy
  , .swe_atready                        (swe_atready) // <   outside-of-hierarchy
  , .swe_afvalid                        (swe_afvalid) // <   outside-of-hierarchy
  , .swe_syncreq                        (swe_syncreq) // <   outside-of-hierarchy
  , .cti_trace_start                    (cti_trace_start) // <   outside-of-hierarchy
  , .cti_trace_stop                     (cti_trace_stop) // <   outside-of-hierarchy
  , .pclkdbg                            (pclkdbg)  // <   outside-of-hierarchy
  , .presetdbgn                         (presetdbgn) // <   outside-of-hierarchy
  , .arct0_paddrdbg                     (arct0_paddrdbg) // <   outside-of-hierarchy
  , .arct0_pseldbg                      (arct0_pseldbg) // <   outside-of-hierarchy
  , .arct0_penabledbg                   (arct0_penabledbg) // <   outside-of-hierarchy
  , .arct0_pwritedbg                    (arct0_pwritedbg) // <   outside-of-hierarchy
  , .arct0_pwdatadbg                    (arct0_pwdatadbg) // <   outside-of-hierarchy
  , .arct0_dbgen                        (arct0_dbgen) // <   outside-of-hierarchy
  , .arct0_niden                        (arct0_niden) // <   outside-of-hierarchy
  , .sl0nl1arc_niden                    (sl0nl1arc_niden) // <   outside-of-hierarchy
  , .sl0nl1arc_dbgen                    (sl0nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl1nl1arc_niden                    (sl1nl1arc_niden) // <   outside-of-hierarchy
  , .sl1nl1arc_dbgen                    (sl1nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl2nl1arc_niden                    (sl2nl1arc_niden) // <   outside-of-hierarchy
  , .sl2nl1arc_dbgen                    (sl2nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl3nl1arc_niden                    (sl3nl1arc_niden) // <   outside-of-hierarchy
  , .sl3nl1arc_dbgen                    (sl3nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl4nl1arc_niden                    (sl4nl1arc_niden) // <   outside-of-hierarchy
  , .sl4nl1arc_dbgen                    (sl4nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl5nl1arc_niden                    (sl5nl1arc_niden) // <   outside-of-hierarchy
  , .sl5nl1arc_dbgen                    (sl5nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl6nl1arc_niden                    (sl6nl1arc_niden) // <   outside-of-hierarchy
  , .sl6nl1arc_dbgen                    (sl6nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl7nl1arc_niden                    (sl7nl1arc_niden) // <   outside-of-hierarchy
  , .sl7nl1arc_dbgen                    (sl7nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl8nl1arc_niden                    (sl8nl1arc_niden) // <   outside-of-hierarchy
  , .sl8nl1arc_dbgen                    (sl8nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl9nl1arc_niden                    (sl9nl1arc_niden) // <   outside-of-hierarchy
  , .sl9nl1arc_dbgen                    (sl9nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl10nl1arc_niden                   (sl10nl1arc_niden) // <   outside-of-hierarchy
  , .sl10nl1arc_dbgen                   (sl10nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl11nl1arc_niden                   (sl11nl1arc_niden) // <   outside-of-hierarchy
  , .sl11nl1arc_dbgen                   (sl11nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl12nl1arc_niden                   (sl12nl1arc_niden) // <   outside-of-hierarchy
  , .sl12nl1arc_dbgen                   (sl12nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl13nl1arc_niden                   (sl13nl1arc_niden) // <   outside-of-hierarchy
  , .sl13nl1arc_dbgen                   (sl13nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl14nl1arc_niden                   (sl14nl1arc_niden) // <   outside-of-hierarchy
  , .sl14nl1arc_dbgen                   (sl14nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl15nl1arc_niden                   (sl15nl1arc_niden) // <   outside-of-hierarchy
  , .sl15nl1arc_dbgen                   (sl15nl1arc_dbgen) // <   outside-of-hierarchy
  , .nl2arc0_dbgen                      (nl2arc0_dbgen) // <   outside-of-hierarchy
  , .nl2arc0_niden                      (nl2arc0_niden) // <   outside-of-hierarchy
  , .nl2arc1_dbgen                      (nl2arc1_dbgen) // <   outside-of-hierarchy
  , .nl2arc1_niden                      (nl2arc1_niden) // <   outside-of-hierarchy
  , .clusternum                         (i_nl2arc0_clusternum) // <   arcsync_top
  , .test_mode                          (test_mode) // <   outside-of-hierarchy
  , .nl2arc0_arc_halt_ack               (i_nl2arc0_arc_halt_ack) //   > arcsync_top
  , .nl2arc0_arc_run_ack                (i_nl2arc0_arc_run_ack) //   > arcsync_top
  , .nl2arc0_sys_sleep_r                (i_nl2arc0_sys_sleep_r) //   > arcsync_top
  , .nl2arc0_sys_sleep_mode_r           (i_nl2arc0_sys_sleep_mode_r) //   > arcsync_top
  , .nl2arc0_sys_halt_r                 (i_nl2arc0_sys_halt_r) //   > arcsync_top
  , .nl2arc0_sys_tf_halt_r              (i_nl2arc0_sys_tf_halt_r) //   > arcsync_top
  , .nl2arc1_arc_halt_ack               (i_nl2arc1_arc_halt_ack) //   > arcsync_top
  , .nl2arc1_arc_run_ack                (i_nl2arc1_arc_run_ack) //   > arcsync_top
  , .nl2arc1_sys_sleep_r                (i_nl2arc1_sys_sleep_r) //   > arcsync_top
  , .nl2arc1_sys_sleep_mode_r           (i_nl2arc1_sys_sleep_mode_r) //   > arcsync_top
  , .nl2arc1_sys_halt_r                 (i_nl2arc1_sys_halt_r) //   > arcsync_top
  , .nl2arc1_sys_tf_halt_r              (i_nl2arc1_sys_tf_halt_r) //   > arcsync_top
  , .sl0nl1arc_arc_halt_ack             (i_sl0nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl0nl1arc_arc_run_ack              (i_sl0nl1arc_arc_run_ack) //   > arcsync_top
  , .sl0nl1arc_sys_sleep_r              (i_sl0nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl0nl1arc_sys_sleep_mode_r         (i_sl0nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl0nl1arc_sys_halt_r               (i_sl0nl1arc_sys_halt_r) //   > arcsync_top
  , .sl0nl1arc_sys_tf_halt_r            (i_sl0nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl1nl1arc_arc_halt_ack             (i_sl1nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl1nl1arc_arc_run_ack              (i_sl1nl1arc_arc_run_ack) //   > arcsync_top
  , .sl1nl1arc_sys_sleep_r              (i_sl1nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl1nl1arc_sys_sleep_mode_r         (i_sl1nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl1nl1arc_sys_halt_r               (i_sl1nl1arc_sys_halt_r) //   > arcsync_top
  , .sl1nl1arc_sys_tf_halt_r            (i_sl1nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl2nl1arc_arc_halt_ack             (i_sl2nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl2nl1arc_arc_run_ack              (i_sl2nl1arc_arc_run_ack) //   > arcsync_top
  , .sl2nl1arc_sys_sleep_r              (i_sl2nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl2nl1arc_sys_sleep_mode_r         (i_sl2nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl2nl1arc_sys_halt_r               (i_sl2nl1arc_sys_halt_r) //   > arcsync_top
  , .sl2nl1arc_sys_tf_halt_r            (i_sl2nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl3nl1arc_arc_halt_ack             (i_sl3nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl3nl1arc_arc_run_ack              (i_sl3nl1arc_arc_run_ack) //   > arcsync_top
  , .sl3nl1arc_sys_sleep_r              (i_sl3nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl3nl1arc_sys_sleep_mode_r         (i_sl3nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl3nl1arc_sys_halt_r               (i_sl3nl1arc_sys_halt_r) //   > arcsync_top
  , .sl3nl1arc_sys_tf_halt_r            (i_sl3nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl4nl1arc_arc_halt_ack             (i_sl4nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl4nl1arc_arc_run_ack              (i_sl4nl1arc_arc_run_ack) //   > arcsync_top
  , .sl4nl1arc_sys_sleep_r              (i_sl4nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl4nl1arc_sys_sleep_mode_r         (i_sl4nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl4nl1arc_sys_halt_r               (i_sl4nl1arc_sys_halt_r) //   > arcsync_top
  , .sl4nl1arc_sys_tf_halt_r            (i_sl4nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl5nl1arc_arc_halt_ack             (i_sl5nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl5nl1arc_arc_run_ack              (i_sl5nl1arc_arc_run_ack) //   > arcsync_top
  , .sl5nl1arc_sys_sleep_r              (i_sl5nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl5nl1arc_sys_sleep_mode_r         (i_sl5nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl5nl1arc_sys_halt_r               (i_sl5nl1arc_sys_halt_r) //   > arcsync_top
  , .sl5nl1arc_sys_tf_halt_r            (i_sl5nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl6nl1arc_arc_halt_ack             (i_sl6nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl6nl1arc_arc_run_ack              (i_sl6nl1arc_arc_run_ack) //   > arcsync_top
  , .sl6nl1arc_sys_sleep_r              (i_sl6nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl6nl1arc_sys_sleep_mode_r         (i_sl6nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl6nl1arc_sys_halt_r               (i_sl6nl1arc_sys_halt_r) //   > arcsync_top
  , .sl6nl1arc_sys_tf_halt_r            (i_sl6nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl7nl1arc_arc_halt_ack             (i_sl7nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl7nl1arc_arc_run_ack              (i_sl7nl1arc_arc_run_ack) //   > arcsync_top
  , .sl7nl1arc_sys_sleep_r              (i_sl7nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl7nl1arc_sys_sleep_mode_r         (i_sl7nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl7nl1arc_sys_halt_r               (i_sl7nl1arc_sys_halt_r) //   > arcsync_top
  , .sl7nl1arc_sys_tf_halt_r            (i_sl7nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl8nl1arc_arc_halt_ack             (i_sl8nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl8nl1arc_arc_run_ack              (i_sl8nl1arc_arc_run_ack) //   > arcsync_top
  , .sl8nl1arc_sys_sleep_r              (i_sl8nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl8nl1arc_sys_sleep_mode_r         (i_sl8nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl8nl1arc_sys_halt_r               (i_sl8nl1arc_sys_halt_r) //   > arcsync_top
  , .sl8nl1arc_sys_tf_halt_r            (i_sl8nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl9nl1arc_arc_halt_ack             (i_sl9nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl9nl1arc_arc_run_ack              (i_sl9nl1arc_arc_run_ack) //   > arcsync_top
  , .sl9nl1arc_sys_sleep_r              (i_sl9nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl9nl1arc_sys_sleep_mode_r         (i_sl9nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl9nl1arc_sys_halt_r               (i_sl9nl1arc_sys_halt_r) //   > arcsync_top
  , .sl9nl1arc_sys_tf_halt_r            (i_sl9nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl10nl1arc_arc_halt_ack            (i_sl10nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl10nl1arc_arc_run_ack             (i_sl10nl1arc_arc_run_ack) //   > arcsync_top
  , .sl10nl1arc_sys_sleep_r             (i_sl10nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl10nl1arc_sys_sleep_mode_r        (i_sl10nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl10nl1arc_sys_halt_r              (i_sl10nl1arc_sys_halt_r) //   > arcsync_top
  , .sl10nl1arc_sys_tf_halt_r           (i_sl10nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl11nl1arc_arc_halt_ack            (i_sl11nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl11nl1arc_arc_run_ack             (i_sl11nl1arc_arc_run_ack) //   > arcsync_top
  , .sl11nl1arc_sys_sleep_r             (i_sl11nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl11nl1arc_sys_sleep_mode_r        (i_sl11nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl11nl1arc_sys_halt_r              (i_sl11nl1arc_sys_halt_r) //   > arcsync_top
  , .sl11nl1arc_sys_tf_halt_r           (i_sl11nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl12nl1arc_arc_halt_ack            (i_sl12nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl12nl1arc_arc_run_ack             (i_sl12nl1arc_arc_run_ack) //   > arcsync_top
  , .sl12nl1arc_sys_sleep_r             (i_sl12nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl12nl1arc_sys_sleep_mode_r        (i_sl12nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl12nl1arc_sys_halt_r              (i_sl12nl1arc_sys_halt_r) //   > arcsync_top
  , .sl12nl1arc_sys_tf_halt_r           (i_sl12nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl13nl1arc_arc_halt_ack            (i_sl13nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl13nl1arc_arc_run_ack             (i_sl13nl1arc_arc_run_ack) //   > arcsync_top
  , .sl13nl1arc_sys_sleep_r             (i_sl13nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl13nl1arc_sys_sleep_mode_r        (i_sl13nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl13nl1arc_sys_halt_r              (i_sl13nl1arc_sys_halt_r) //   > arcsync_top
  , .sl13nl1arc_sys_tf_halt_r           (i_sl13nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl14nl1arc_arc_halt_ack            (i_sl14nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl14nl1arc_arc_run_ack             (i_sl14nl1arc_arc_run_ack) //   > arcsync_top
  , .sl14nl1arc_sys_sleep_r             (i_sl14nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl14nl1arc_sys_sleep_mode_r        (i_sl14nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl14nl1arc_sys_halt_r              (i_sl14nl1arc_sys_halt_r) //   > arcsync_top
  , .sl14nl1arc_sys_tf_halt_r           (i_sl14nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .sl15nl1arc_arc_halt_ack            (i_sl15nl1arc_arc_halt_ack) //   > arcsync_top
  , .sl15nl1arc_arc_run_ack             (i_sl15nl1arc_arc_run_ack) //   > arcsync_top
  , .sl15nl1arc_sys_sleep_r             (i_sl15nl1arc_sys_sleep_r) //   > arcsync_top
  , .sl15nl1arc_sys_sleep_mode_r        (i_sl15nl1arc_sys_sleep_mode_r) //   > arcsync_top
  , .sl15nl1arc_sys_halt_r              (i_sl15nl1arc_sys_halt_r) //   > arcsync_top
  , .sl15nl1arc_sys_tf_halt_r           (i_sl15nl1arc_sys_tf_halt_r) //   > arcsync_top
  , .nl2arc0_wdt_reset_error            (i_nl2arc0_wdt_reset_error) //   > unconnected
  , .nl2arc0_wdt_reset_wdt_clk_error    (i_nl2arc0_wdt_reset_wdt_clk_error) //   > unconnected
  , .nl2arc1_wdt_reset_error            (i_nl2arc1_wdt_reset_error) //   > unconnected
  , .nl2arc1_wdt_reset_wdt_clk_error    (i_nl2arc1_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl0nl1arc_wdt_reset_error          (i_sl0nl1arc_wdt_reset_error) //   > unconnected
  , .sl0nl1arc_wdt_reset_wdt_clk_error  (i_sl0nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl1nl1arc_wdt_reset_error          (i_sl1nl1arc_wdt_reset_error) //   > unconnected
  , .sl1nl1arc_wdt_reset_wdt_clk_error  (i_sl1nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl2nl1arc_wdt_reset_error          (i_sl2nl1arc_wdt_reset_error) //   > unconnected
  , .sl2nl1arc_wdt_reset_wdt_clk_error  (i_sl2nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl3nl1arc_wdt_reset_error          (i_sl3nl1arc_wdt_reset_error) //   > unconnected
  , .sl3nl1arc_wdt_reset_wdt_clk_error  (i_sl3nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl4nl1arc_wdt_reset_error          (i_sl4nl1arc_wdt_reset_error) //   > unconnected
  , .sl4nl1arc_wdt_reset_wdt_clk_error  (i_sl4nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl5nl1arc_wdt_reset_error          (i_sl5nl1arc_wdt_reset_error) //   > unconnected
  , .sl5nl1arc_wdt_reset_wdt_clk_error  (i_sl5nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl6nl1arc_wdt_reset_error          (i_sl6nl1arc_wdt_reset_error) //   > unconnected
  , .sl6nl1arc_wdt_reset_wdt_clk_error  (i_sl6nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl7nl1arc_wdt_reset_error          (i_sl7nl1arc_wdt_reset_error) //   > unconnected
  , .sl7nl1arc_wdt_reset_wdt_clk_error  (i_sl7nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl8nl1arc_wdt_reset_error          (i_sl8nl1arc_wdt_reset_error) //   > unconnected
  , .sl8nl1arc_wdt_reset_wdt_clk_error  (i_sl8nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl9nl1arc_wdt_reset_error          (i_sl9nl1arc_wdt_reset_error) //   > unconnected
  , .sl9nl1arc_wdt_reset_wdt_clk_error  (i_sl9nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl10nl1arc_wdt_reset_error         (i_sl10nl1arc_wdt_reset_error) //   > unconnected
  , .sl10nl1arc_wdt_reset_wdt_clk_error (i_sl10nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl11nl1arc_wdt_reset_error         (i_sl11nl1arc_wdt_reset_error) //   > unconnected
  , .sl11nl1arc_wdt_reset_wdt_clk_error (i_sl11nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl12nl1arc_wdt_reset_error         (i_sl12nl1arc_wdt_reset_error) //   > unconnected
  , .sl12nl1arc_wdt_reset_wdt_clk_error (i_sl12nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl13nl1arc_wdt_reset_error         (i_sl13nl1arc_wdt_reset_error) //   > unconnected
  , .sl13nl1arc_wdt_reset_wdt_clk_error (i_sl13nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl14nl1arc_wdt_reset_error         (i_sl14nl1arc_wdt_reset_error) //   > unconnected
  , .sl14nl1arc_wdt_reset_wdt_clk_error (i_sl14nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .sl15nl1arc_wdt_reset_error         (i_sl15nl1arc_wdt_reset_error) //   > unconnected
  , .sl15nl1arc_wdt_reset_wdt_clk_error (i_sl15nl1arc_wdt_reset_wdt_clk_error) //   > unconnected
  , .npu_mst0_axi_arid                  (npu_mst0_axi_arid) //   > alb_mss_fab
  , .npu_mst0_axi_arvalid               (npu_mst0_axi_arvalid) //   > alb_mss_fab
  , .npu_mst0_axi_araddr                (npu_mst0_axi_araddr) //   > alb_mss_fab
  , .npu_mst0_axi_arburst               (npu_mst0_axi_arburst) //   > alb_mss_fab
  , .npu_mst0_axi_arsize                (npu_mst0_axi_arsize) //   > alb_mss_fab
  , .npu_mst0_axi_arlock                (npu_mst0_axi_arlock) //   > alb_mss_fab
  , .npu_mst0_axi_arlen                 (npu_mst0_axi_arlen) //   > alb_mss_fab
  , .npu_mst0_axi_arcache               (npu_mst0_axi_arcache) //   > alb_mss_fab
  , .npu_mst0_axi_arprot                (npu_mst0_axi_arprot) //   > alb_mss_fab
  , .npu_mst0_axi_rready                (npu_mst0_axi_rready) //   > alb_mss_fab
  , .npu_mst0_axi_awid                  (npu_mst0_axi_awid) //   > alb_mss_fab
  , .npu_mst0_axi_awvalid               (npu_mst0_axi_awvalid) //   > alb_mss_fab
  , .npu_mst0_axi_awaddr                (npu_mst0_axi_awaddr) //   > alb_mss_fab
  , .npu_mst0_axi_awburst               (npu_mst0_axi_awburst) //   > alb_mss_fab
  , .npu_mst0_axi_awsize                (npu_mst0_axi_awsize) //   > alb_mss_fab
  , .npu_mst0_axi_awlock                (npu_mst0_axi_awlock) //   > alb_mss_fab
  , .npu_mst0_axi_awlen                 (npu_mst0_axi_awlen) //   > alb_mss_fab
  , .npu_mst0_axi_awcache               (npu_mst0_axi_awcache) //   > alb_mss_fab
  , .npu_mst0_axi_awprot                (npu_mst0_axi_awprot) //   > alb_mss_fab
  , .npu_mst0_axi_wvalid                (npu_mst0_axi_wvalid) //   > alb_mss_fab
  , .npu_mst0_axi_wdata                 (npu_mst0_axi_wdata) //   > alb_mss_fab
  , .npu_mst0_axi_wstrb                 (npu_mst0_axi_wstrb) //   > alb_mss_fab
  , .npu_mst0_axi_wlast                 (npu_mst0_axi_wlast) //   > alb_mss_fab
  , .npu_mst0_axi_bready                (npu_mst0_axi_bready) //   > alb_mss_fab
  , .npu_mst1_axi_arid                  (npu_mst1_axi_arid) //   > alb_mss_fab
  , .npu_mst1_axi_arvalid               (npu_mst1_axi_arvalid) //   > alb_mss_fab
  , .npu_mst1_axi_araddr                (npu_mst1_axi_araddr) //   > alb_mss_fab
  , .npu_mst1_axi_arburst               (npu_mst1_axi_arburst) //   > alb_mss_fab
  , .npu_mst1_axi_arsize                (npu_mst1_axi_arsize) //   > alb_mss_fab
  , .npu_mst1_axi_arlock                (npu_mst1_axi_arlock) //   > alb_mss_fab
  , .npu_mst1_axi_arlen                 (npu_mst1_axi_arlen) //   > alb_mss_fab
  , .npu_mst1_axi_arcache               (npu_mst1_axi_arcache) //   > alb_mss_fab
  , .npu_mst1_axi_arprot                (npu_mst1_axi_arprot) //   > alb_mss_fab
  , .npu_mst1_axi_rready                (npu_mst1_axi_rready) //   > alb_mss_fab
  , .npu_mst1_axi_awid                  (npu_mst1_axi_awid) //   > alb_mss_fab
  , .npu_mst1_axi_awvalid               (npu_mst1_axi_awvalid) //   > alb_mss_fab
  , .npu_mst1_axi_awaddr                (npu_mst1_axi_awaddr) //   > alb_mss_fab
  , .npu_mst1_axi_awburst               (npu_mst1_axi_awburst) //   > alb_mss_fab
  , .npu_mst1_axi_awsize                (npu_mst1_axi_awsize) //   > alb_mss_fab
  , .npu_mst1_axi_awlock                (npu_mst1_axi_awlock) //   > alb_mss_fab
  , .npu_mst1_axi_awlen                 (npu_mst1_axi_awlen) //   > alb_mss_fab
  , .npu_mst1_axi_awcache               (npu_mst1_axi_awcache) //   > alb_mss_fab
  , .npu_mst1_axi_awprot                (npu_mst1_axi_awprot) //   > alb_mss_fab
  , .npu_mst1_axi_wvalid                (npu_mst1_axi_wvalid) //   > alb_mss_fab
  , .npu_mst1_axi_wdata                 (npu_mst1_axi_wdata) //   > alb_mss_fab
  , .npu_mst1_axi_wstrb                 (npu_mst1_axi_wstrb) //   > alb_mss_fab
  , .npu_mst1_axi_wlast                 (npu_mst1_axi_wlast) //   > alb_mss_fab
  , .npu_mst1_axi_bready                (npu_mst1_axi_bready) //   > alb_mss_fab
  , .npu_mst2_axi_arid                  (npu_mst2_axi_arid) //   > alb_mss_fab
  , .npu_mst2_axi_arvalid               (npu_mst2_axi_arvalid) //   > alb_mss_fab
  , .npu_mst2_axi_araddr                (npu_mst2_axi_araddr) //   > alb_mss_fab
  , .npu_mst2_axi_arburst               (npu_mst2_axi_arburst) //   > alb_mss_fab
  , .npu_mst2_axi_arsize                (npu_mst2_axi_arsize) //   > alb_mss_fab
  , .npu_mst2_axi_arlock                (npu_mst2_axi_arlock) //   > alb_mss_fab
  , .npu_mst2_axi_arlen                 (npu_mst2_axi_arlen) //   > alb_mss_fab
  , .npu_mst2_axi_arcache               (npu_mst2_axi_arcache) //   > alb_mss_fab
  , .npu_mst2_axi_arprot                (npu_mst2_axi_arprot) //   > alb_mss_fab
  , .npu_mst2_axi_rready                (npu_mst2_axi_rready) //   > alb_mss_fab
  , .npu_mst2_axi_awid                  (npu_mst2_axi_awid) //   > alb_mss_fab
  , .npu_mst2_axi_awvalid               (npu_mst2_axi_awvalid) //   > alb_mss_fab
  , .npu_mst2_axi_awaddr                (npu_mst2_axi_awaddr) //   > alb_mss_fab
  , .npu_mst2_axi_awburst               (npu_mst2_axi_awburst) //   > alb_mss_fab
  , .npu_mst2_axi_awsize                (npu_mst2_axi_awsize) //   > alb_mss_fab
  , .npu_mst2_axi_awlock                (npu_mst2_axi_awlock) //   > alb_mss_fab
  , .npu_mst2_axi_awlen                 (npu_mst2_axi_awlen) //   > alb_mss_fab
  , .npu_mst2_axi_awcache               (npu_mst2_axi_awcache) //   > alb_mss_fab
  , .npu_mst2_axi_awprot                (npu_mst2_axi_awprot) //   > alb_mss_fab
  , .npu_mst2_axi_wvalid                (npu_mst2_axi_wvalid) //   > alb_mss_fab
  , .npu_mst2_axi_wdata                 (npu_mst2_axi_wdata) //   > alb_mss_fab
  , .npu_mst2_axi_wstrb                 (npu_mst2_axi_wstrb) //   > alb_mss_fab
  , .npu_mst2_axi_wlast                 (npu_mst2_axi_wlast) //   > alb_mss_fab
  , .npu_mst2_axi_bready                (npu_mst2_axi_bready) //   > alb_mss_fab
  , .npu_mst3_axi_arid                  (npu_mst3_axi_arid) //   > alb_mss_fab
  , .npu_mst3_axi_arvalid               (npu_mst3_axi_arvalid) //   > alb_mss_fab
  , .npu_mst3_axi_araddr                (npu_mst3_axi_araddr) //   > alb_mss_fab
  , .npu_mst3_axi_arburst               (npu_mst3_axi_arburst) //   > alb_mss_fab
  , .npu_mst3_axi_arsize                (npu_mst3_axi_arsize) //   > alb_mss_fab
  , .npu_mst3_axi_arlock                (npu_mst3_axi_arlock) //   > alb_mss_fab
  , .npu_mst3_axi_arlen                 (npu_mst3_axi_arlen) //   > alb_mss_fab
  , .npu_mst3_axi_arcache               (npu_mst3_axi_arcache) //   > alb_mss_fab
  , .npu_mst3_axi_arprot                (npu_mst3_axi_arprot) //   > alb_mss_fab
  , .npu_mst3_axi_rready                (npu_mst3_axi_rready) //   > alb_mss_fab
  , .npu_mst3_axi_awid                  (npu_mst3_axi_awid) //   > alb_mss_fab
  , .npu_mst3_axi_awvalid               (npu_mst3_axi_awvalid) //   > alb_mss_fab
  , .npu_mst3_axi_awaddr                (npu_mst3_axi_awaddr) //   > alb_mss_fab
  , .npu_mst3_axi_awburst               (npu_mst3_axi_awburst) //   > alb_mss_fab
  , .npu_mst3_axi_awsize                (npu_mst3_axi_awsize) //   > alb_mss_fab
  , .npu_mst3_axi_awlock                (npu_mst3_axi_awlock) //   > alb_mss_fab
  , .npu_mst3_axi_awlen                 (npu_mst3_axi_awlen) //   > alb_mss_fab
  , .npu_mst3_axi_awcache               (npu_mst3_axi_awcache) //   > alb_mss_fab
  , .npu_mst3_axi_awprot                (npu_mst3_axi_awprot) //   > alb_mss_fab
  , .npu_mst3_axi_wvalid                (npu_mst3_axi_wvalid) //   > alb_mss_fab
  , .npu_mst3_axi_wdata                 (npu_mst3_axi_wdata) //   > alb_mss_fab
  , .npu_mst3_axi_wstrb                 (npu_mst3_axi_wstrb) //   > alb_mss_fab
  , .npu_mst3_axi_wlast                 (npu_mst3_axi_wlast) //   > alb_mss_fab
  , .npu_mst3_axi_bready                (npu_mst3_axi_bready) //   > alb_mss_fab
  , .npu_mst4_axi_arid                  (npu_mst4_axi_arid) //   > alb_mss_fab
  , .npu_mst4_axi_arvalid               (npu_mst4_axi_arvalid) //   > alb_mss_fab
  , .npu_mst4_axi_araddr                (npu_mst4_axi_araddr) //   > alb_mss_fab
  , .npu_mst4_axi_arburst               (npu_mst4_axi_arburst) //   > alb_mss_fab
  , .npu_mst4_axi_arsize                (npu_mst4_axi_arsize) //   > alb_mss_fab
  , .npu_mst4_axi_arlock                (npu_mst4_axi_arlock) //   > alb_mss_fab
  , .npu_mst4_axi_arlen                 (npu_mst4_axi_arlen) //   > alb_mss_fab
  , .npu_mst4_axi_arcache               (npu_mst4_axi_arcache) //   > alb_mss_fab
  , .npu_mst4_axi_arprot                (npu_mst4_axi_arprot) //   > alb_mss_fab
  , .npu_mst4_axi_rready                (npu_mst4_axi_rready) //   > alb_mss_fab
  , .npu_mst4_axi_awid                  (npu_mst4_axi_awid) //   > alb_mss_fab
  , .npu_mst4_axi_awvalid               (npu_mst4_axi_awvalid) //   > alb_mss_fab
  , .npu_mst4_axi_awaddr                (npu_mst4_axi_awaddr) //   > alb_mss_fab
  , .npu_mst4_axi_awburst               (npu_mst4_axi_awburst) //   > alb_mss_fab
  , .npu_mst4_axi_awsize                (npu_mst4_axi_awsize) //   > alb_mss_fab
  , .npu_mst4_axi_awlock                (npu_mst4_axi_awlock) //   > alb_mss_fab
  , .npu_mst4_axi_awlen                 (npu_mst4_axi_awlen) //   > alb_mss_fab
  , .npu_mst4_axi_awcache               (npu_mst4_axi_awcache) //   > alb_mss_fab
  , .npu_mst4_axi_awprot                (npu_mst4_axi_awprot) //   > alb_mss_fab
  , .npu_mst4_axi_wvalid                (npu_mst4_axi_wvalid) //   > alb_mss_fab
  , .npu_mst4_axi_wdata                 (npu_mst4_axi_wdata) //   > alb_mss_fab
  , .npu_mst4_axi_wstrb                 (npu_mst4_axi_wstrb) //   > alb_mss_fab
  , .npu_mst4_axi_wlast                 (npu_mst4_axi_wlast) //   > alb_mss_fab
  , .npu_mst4_axi_bready                (npu_mst4_axi_bready) //   > alb_mss_fab
  , .npu_dmi0_axi_arready               (npu_dmi0_axi_arready) //   > alb_mss_fab
  , .npu_dmi0_axi_rid                   (npu_dmi0_axi_rid) //   > alb_mss_fab
  , .npu_dmi0_axi_rvalid                (npu_dmi0_axi_rvalid) //   > alb_mss_fab
  , .npu_dmi0_axi_rdata                 (npu_dmi0_axi_rdata) //   > alb_mss_fab
  , .npu_dmi0_axi_rresp                 (npu_dmi0_axi_rresp) //   > alb_mss_fab
  , .npu_dmi0_axi_rlast                 (npu_dmi0_axi_rlast) //   > alb_mss_fab
  , .npu_dmi0_axi_awready               (npu_dmi0_axi_awready) //   > alb_mss_fab
  , .npu_dmi0_axi_wready                (npu_dmi0_axi_wready) //   > alb_mss_fab
  , .npu_dmi0_axi_bid                   (npu_dmi0_axi_bid) //   > alb_mss_fab
  , .npu_dmi0_axi_bvalid                (npu_dmi0_axi_bvalid) //   > alb_mss_fab
  , .npu_dmi0_axi_bresp                 (npu_dmi0_axi_bresp) //   > alb_mss_fab
  , .npu_cfg_axi_arready                (npu_cfg_axi_arready) //   > alb_mss_fab
  , .npu_cfg_axi_rid                    (npu_cfg_axi_rid) //   > alb_mss_fab
  , .npu_cfg_axi_rvalid                 (npu_cfg_axi_rvalid) //   > alb_mss_fab
  , .npu_cfg_axi_rdata                  (npu_cfg_axi_rdata) //   > alb_mss_fab
  , .npu_cfg_axi_rresp                  (npu_cfg_axi_rresp) //   > alb_mss_fab
  , .npu_cfg_axi_rlast                  (npu_cfg_axi_rlast) //   > alb_mss_fab
  , .npu_cfg_axi_awready                (npu_cfg_axi_awready) //   > alb_mss_fab
  , .npu_cfg_axi_wready                 (npu_cfg_axi_wready) //   > alb_mss_fab
  , .npu_cfg_axi_bid                    (npu_cfg_axi_bid) //   > alb_mss_fab
  , .npu_cfg_axi_bvalid                 (npu_cfg_axi_bvalid) //   > alb_mss_fab
  , .npu_cfg_axi_bresp                  (npu_cfg_axi_bresp) //   > alb_mss_fab
  , .npu_mst1_axi_arsid                 (npu_mst1_axi_arsid) //   > core_sys_stub
  , .npu_mst1_axi_arssid                (npu_mst1_axi_arssid) //   > core_sys_stub
  , .npu_mst1_axi_awsid                 (npu_mst1_axi_awsid) //   > core_sys_stub
  , .npu_mst1_axi_awssid                (npu_mst1_axi_awssid) //   > core_sys_stub
  , .npu_mst2_axi_arsid                 (npu_mst2_axi_arsid) //   > core_sys_stub
  , .npu_mst2_axi_arssid                (npu_mst2_axi_arssid) //   > core_sys_stub
  , .npu_mst2_axi_awsid                 (npu_mst2_axi_awsid) //   > core_sys_stub
  , .npu_mst2_axi_awssid                (npu_mst2_axi_awssid) //   > core_sys_stub
  , .npu_mst3_axi_arsid                 (npu_mst3_axi_arsid) //   > core_sys_stub
  , .npu_mst3_axi_arssid                (npu_mst3_axi_arssid) //   > core_sys_stub
  , .npu_mst3_axi_awsid                 (npu_mst3_axi_awsid) //   > core_sys_stub
  , .npu_mst3_axi_awssid                (npu_mst3_axi_awssid) //   > core_sys_stub
  , .npu_mst4_axi_arsid                 (npu_mst4_axi_arsid) //   > core_sys_stub
  , .npu_mst4_axi_arssid                (npu_mst4_axi_arssid) //   > core_sys_stub
  , .npu_mst4_axi_awsid                 (npu_mst4_axi_awsid) //   > core_sys_stub
  , .npu_mst4_axi_awssid                (npu_mst4_axi_awssid) //   > core_sys_stub
  , .sl0_ecc_sbe                        (sl0_ecc_sbe) //   > core_sys_stub
  , .sl0_ecc_dbe                        (sl0_ecc_dbe) //   > core_sys_stub
  , .sl1_ecc_sbe                        (sl1_ecc_sbe) //   > core_sys_stub
  , .sl1_ecc_dbe                        (sl1_ecc_dbe) //   > core_sys_stub
  , .sl2_ecc_sbe                        (sl2_ecc_sbe) //   > core_sys_stub
  , .sl2_ecc_dbe                        (sl2_ecc_dbe) //   > core_sys_stub
  , .sl3_ecc_sbe                        (sl3_ecc_sbe) //   > core_sys_stub
  , .sl3_ecc_dbe                        (sl3_ecc_dbe) //   > core_sys_stub
  , .sl4_ecc_sbe                        (sl4_ecc_sbe) //   > core_sys_stub
  , .sl4_ecc_dbe                        (sl4_ecc_dbe) //   > core_sys_stub
  , .sl5_ecc_sbe                        (sl5_ecc_sbe) //   > core_sys_stub
  , .sl5_ecc_dbe                        (sl5_ecc_dbe) //   > core_sys_stub
  , .sl6_ecc_sbe                        (sl6_ecc_sbe) //   > core_sys_stub
  , .sl6_ecc_dbe                        (sl6_ecc_dbe) //   > core_sys_stub
  , .sl7_ecc_sbe                        (sl7_ecc_sbe) //   > core_sys_stub
  , .sl7_ecc_dbe                        (sl7_ecc_dbe) //   > core_sys_stub
  , .sl8_ecc_sbe                        (sl8_ecc_sbe) //   > core_sys_stub
  , .sl8_ecc_dbe                        (sl8_ecc_dbe) //   > core_sys_stub
  , .sl9_ecc_sbe                        (sl9_ecc_sbe) //   > core_sys_stub
  , .sl9_ecc_dbe                        (sl9_ecc_dbe) //   > core_sys_stub
  , .sl10_ecc_sbe                       (sl10_ecc_sbe) //   > core_sys_stub
  , .sl10_ecc_dbe                       (sl10_ecc_dbe) //   > core_sys_stub
  , .sl11_ecc_sbe                       (sl11_ecc_sbe) //   > core_sys_stub
  , .sl11_ecc_dbe                       (sl11_ecc_dbe) //   > core_sys_stub
  , .sl12_ecc_sbe                       (sl12_ecc_sbe) //   > core_sys_stub
  , .sl12_ecc_dbe                       (sl12_ecc_dbe) //   > core_sys_stub
  , .sl13_ecc_sbe                       (sl13_ecc_sbe) //   > core_sys_stub
  , .sl13_ecc_dbe                       (sl13_ecc_dbe) //   > core_sys_stub
  , .sl14_ecc_sbe                       (sl14_ecc_sbe) //   > core_sys_stub
  , .sl14_ecc_dbe                       (sl14_ecc_dbe) //   > core_sys_stub
  , .sl15_ecc_sbe                       (sl15_ecc_sbe) //   > core_sys_stub
  , .sl15_ecc_dbe                       (sl15_ecc_dbe) //   > core_sys_stub
  , .grp0_scm_dbank_sbe                 (grp0_scm_dbank_sbe) //   > core_sys_stub
  , .grp0_scm_dbank_dbe                 (grp0_scm_dbank_dbe) //   > core_sys_stub
  , .grp1_scm_dbank_sbe                 (grp1_scm_dbank_sbe) //   > core_sys_stub
  , .grp1_scm_dbank_dbe                 (grp1_scm_dbank_dbe) //   > core_sys_stub
  , .grp2_scm_dbank_sbe                 (grp2_scm_dbank_sbe) //   > core_sys_stub
  , .grp2_scm_dbank_dbe                 (grp2_scm_dbank_dbe) //   > core_sys_stub
  , .grp3_scm_dbank_sbe                 (grp3_scm_dbank_sbe) //   > core_sys_stub
  , .grp3_scm_dbank_dbe                 (grp3_scm_dbank_dbe) //   > core_sys_stub
  , .nl2arc0_ecc_sbe                    (nl2arc0_ecc_sbe) //   > core_sys_stub
  , .nl2arc0_ecc_dbe                    (nl2arc0_ecc_dbe) //   > core_sys_stub
  , .nl2arc1_ecc_sbe                    (nl2arc1_ecc_sbe) //   > core_sys_stub
  , .nl2arc1_ecc_dbe                    (nl2arc1_ecc_dbe) //   > core_sys_stub
  , .nl2arc0_evt_vm_irq                 (nl2arc0_evt_vm_irq) //   > outside-of-hierarchy
  , .nl2arc1_evt_vm_irq                 (nl2arc1_evt_vm_irq) //   > outside-of-hierarchy
  , .atdata                             (atdata)   //   > outside-of-hierarchy
  , .atbytes                            (atbytes)  //   > outside-of-hierarchy
  , .atid                               (atid)     //   > outside-of-hierarchy
  , .atvalid                            (atvalid)  //   > outside-of-hierarchy
  , .afready                            (afready)  //   > outside-of-hierarchy
  , .swe_atdata                         (swe_atdata) //   > outside-of-hierarchy
  , .swe_atbytes                        (swe_atbytes) //   > outside-of-hierarchy
  , .swe_atid                           (swe_atid) //   > outside-of-hierarchy
  , .swe_atvalid                        (swe_atvalid) //   > outside-of-hierarchy
  , .swe_afready                        (swe_afready) //   > outside-of-hierarchy
  , .cti_rtt_filters                    (cti_rtt_filters) //   > outside-of-hierarchy
  , .arct0_preadydbg                    (arct0_preadydbg) //   > outside-of-hierarchy
  , .arct0_prdatadbg                    (arct0_prdatadbg) //   > outside-of-hierarchy
  , .arct0_pslverrdbg                   (arct0_pslverrdbg) //   > outside-of-hierarchy
  );

// Instantiation of module arcsync_top
arcsync_top iarcsync_top(
    .arcsync_axi_arvalid           (arcsync_axi_arvalid) // <   alb_mss_fab
  , .arcsync_axi_arid              (arcsync_axi_arid) // <   alb_mss_fab
  , .arcsync_axi_araddr            (arcsync_axi_araddr) // <   alb_mss_fab
  , .arcsync_axi_arcache           (arcsync_axi_arcache) // <   alb_mss_fab
  , .arcsync_axi_arprot            (arcsync_axi_arprot) // <   alb_mss_fab
  , .arcsync_axi_arlock            (arcsync_axi_arlock) // <   alb_mss_fab
  , .arcsync_axi_arburst           (arcsync_axi_arburst) // <   alb_mss_fab
  , .arcsync_axi_arlen             (arcsync_axi_arlen) // <   alb_mss_fab
  , .arcsync_axi_arsize            (arcsync_axi_arsize) // <   alb_mss_fab
  , .arcsync_axi_rready            (arcsync_axi_rready) // <   alb_mss_fab
  , .arcsync_axi_awvalid           (arcsync_axi_awvalid) // <   alb_mss_fab
  , .arcsync_axi_awid              (arcsync_axi_awid) // <   alb_mss_fab
  , .arcsync_axi_awaddr            (arcsync_axi_awaddr) // <   alb_mss_fab
  , .arcsync_axi_awcache           (arcsync_axi_awcache) // <   alb_mss_fab
  , .arcsync_axi_awprot            (arcsync_axi_awprot) // <   alb_mss_fab
  , .arcsync_axi_awlock            (arcsync_axi_awlock) // <   alb_mss_fab
  , .arcsync_axi_awburst           (arcsync_axi_awburst) // <   alb_mss_fab
  , .arcsync_axi_awlen             (arcsync_axi_awlen) // <   alb_mss_fab
  , .arcsync_axi_awsize            (arcsync_axi_awsize) // <   alb_mss_fab
  , .arcsync_axi_wvalid            (arcsync_axi_wvalid) // <   alb_mss_fab
  , .arcsync_axi_wdata             (arcsync_axi_wdata) // <   alb_mss_fab
  , .arcsync_axi_wstrb             (arcsync_axi_wstrb) // <   alb_mss_fab
  , .arcsync_axi_wlast             (arcsync_axi_wlast) // <   alb_mss_fab
  , .arcsync_axi_bready            (arcsync_axi_bready) // <   alb_mss_fab
  , .nl2arc0_arc_halt_ack_a        (i_nl2arc0_arc_halt_ack) // <   npu_top
  , .nl2arc0_ext_arc_halt_req_a    (nl2arc0_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .nl2arc0_arc_run_ack_a         (i_nl2arc0_arc_run_ack) // <   npu_top
  , .nl2arc0_ext_arc_run_req_a     (nl2arc0_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .nl2arc0_sys_sleep_r           (i_nl2arc0_sys_sleep_r) // <   npu_top
  , .nl2arc0_sys_sleep_mode_r      (i_nl2arc0_sys_sleep_mode_r) // <   npu_top
  , .nl2arc0_sys_halt_r            (i_nl2arc0_sys_halt_r) // <   npu_top
  , .nl2arc0_sys_tf_halt_r         (i_nl2arc0_sys_tf_halt_r) // <   npu_top
  , .nl2arc1_arc_halt_ack_a        (i_nl2arc1_arc_halt_ack) // <   npu_top
  , .nl2arc1_ext_arc_halt_req_a    (nl2arc1_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .nl2arc1_arc_run_ack_a         (i_nl2arc1_arc_run_ack) // <   npu_top
  , .nl2arc1_ext_arc_run_req_a     (nl2arc1_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .nl2arc1_sys_sleep_r           (i_nl2arc1_sys_sleep_r) // <   npu_top
  , .nl2arc1_sys_sleep_mode_r      (i_nl2arc1_sys_sleep_mode_r) // <   npu_top
  , .nl2arc1_sys_halt_r            (i_nl2arc1_sys_halt_r) // <   npu_top
  , .nl2arc1_sys_tf_halt_r         (i_nl2arc1_sys_tf_halt_r) // <   npu_top
  , .sl0nl1arc_arc_halt_ack_a      (i_sl0nl1arc_arc_halt_ack) // <   npu_top
  , .sl0nl1arc_ext_arc_halt_req_a  (sl0nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl0nl1arc_arc_run_ack_a       (i_sl0nl1arc_arc_run_ack) // <   npu_top
  , .sl0nl1arc_ext_arc_run_req_a   (sl0nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl0nl1arc_sys_sleep_r         (i_sl0nl1arc_sys_sleep_r) // <   npu_top
  , .sl0nl1arc_sys_sleep_mode_r    (i_sl0nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl0nl1arc_sys_halt_r          (i_sl0nl1arc_sys_halt_r) // <   npu_top
  , .sl0nl1arc_sys_tf_halt_r       (i_sl0nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl1nl1arc_arc_halt_ack_a      (i_sl1nl1arc_arc_halt_ack) // <   npu_top
  , .sl1nl1arc_ext_arc_halt_req_a  (sl1nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl1nl1arc_arc_run_ack_a       (i_sl1nl1arc_arc_run_ack) // <   npu_top
  , .sl1nl1arc_ext_arc_run_req_a   (sl1nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl1nl1arc_sys_sleep_r         (i_sl1nl1arc_sys_sleep_r) // <   npu_top
  , .sl1nl1arc_sys_sleep_mode_r    (i_sl1nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl1nl1arc_sys_halt_r          (i_sl1nl1arc_sys_halt_r) // <   npu_top
  , .sl1nl1arc_sys_tf_halt_r       (i_sl1nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl2nl1arc_arc_halt_ack_a      (i_sl2nl1arc_arc_halt_ack) // <   npu_top
  , .sl2nl1arc_ext_arc_halt_req_a  (sl2nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl2nl1arc_arc_run_ack_a       (i_sl2nl1arc_arc_run_ack) // <   npu_top
  , .sl2nl1arc_ext_arc_run_req_a   (sl2nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl2nl1arc_sys_sleep_r         (i_sl2nl1arc_sys_sleep_r) // <   npu_top
  , .sl2nl1arc_sys_sleep_mode_r    (i_sl2nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl2nl1arc_sys_halt_r          (i_sl2nl1arc_sys_halt_r) // <   npu_top
  , .sl2nl1arc_sys_tf_halt_r       (i_sl2nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl3nl1arc_arc_halt_ack_a      (i_sl3nl1arc_arc_halt_ack) // <   npu_top
  , .sl3nl1arc_ext_arc_halt_req_a  (sl3nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl3nl1arc_arc_run_ack_a       (i_sl3nl1arc_arc_run_ack) // <   npu_top
  , .sl3nl1arc_ext_arc_run_req_a   (sl3nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl3nl1arc_sys_sleep_r         (i_sl3nl1arc_sys_sleep_r) // <   npu_top
  , .sl3nl1arc_sys_sleep_mode_r    (i_sl3nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl3nl1arc_sys_halt_r          (i_sl3nl1arc_sys_halt_r) // <   npu_top
  , .sl3nl1arc_sys_tf_halt_r       (i_sl3nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl4nl1arc_arc_halt_ack_a      (i_sl4nl1arc_arc_halt_ack) // <   npu_top
  , .sl4nl1arc_ext_arc_halt_req_a  (sl4nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl4nl1arc_arc_run_ack_a       (i_sl4nl1arc_arc_run_ack) // <   npu_top
  , .sl4nl1arc_ext_arc_run_req_a   (sl4nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl4nl1arc_sys_sleep_r         (i_sl4nl1arc_sys_sleep_r) // <   npu_top
  , .sl4nl1arc_sys_sleep_mode_r    (i_sl4nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl4nl1arc_sys_halt_r          (i_sl4nl1arc_sys_halt_r) // <   npu_top
  , .sl4nl1arc_sys_tf_halt_r       (i_sl4nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl5nl1arc_arc_halt_ack_a      (i_sl5nl1arc_arc_halt_ack) // <   npu_top
  , .sl5nl1arc_ext_arc_halt_req_a  (sl5nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl5nl1arc_arc_run_ack_a       (i_sl5nl1arc_arc_run_ack) // <   npu_top
  , .sl5nl1arc_ext_arc_run_req_a   (sl5nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl5nl1arc_sys_sleep_r         (i_sl5nl1arc_sys_sleep_r) // <   npu_top
  , .sl5nl1arc_sys_sleep_mode_r    (i_sl5nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl5nl1arc_sys_halt_r          (i_sl5nl1arc_sys_halt_r) // <   npu_top
  , .sl5nl1arc_sys_tf_halt_r       (i_sl5nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl6nl1arc_arc_halt_ack_a      (i_sl6nl1arc_arc_halt_ack) // <   npu_top
  , .sl6nl1arc_ext_arc_halt_req_a  (sl6nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl6nl1arc_arc_run_ack_a       (i_sl6nl1arc_arc_run_ack) // <   npu_top
  , .sl6nl1arc_ext_arc_run_req_a   (sl6nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl6nl1arc_sys_sleep_r         (i_sl6nl1arc_sys_sleep_r) // <   npu_top
  , .sl6nl1arc_sys_sleep_mode_r    (i_sl6nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl6nl1arc_sys_halt_r          (i_sl6nl1arc_sys_halt_r) // <   npu_top
  , .sl6nl1arc_sys_tf_halt_r       (i_sl6nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl7nl1arc_arc_halt_ack_a      (i_sl7nl1arc_arc_halt_ack) // <   npu_top
  , .sl7nl1arc_ext_arc_halt_req_a  (sl7nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl7nl1arc_arc_run_ack_a       (i_sl7nl1arc_arc_run_ack) // <   npu_top
  , .sl7nl1arc_ext_arc_run_req_a   (sl7nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl7nl1arc_sys_sleep_r         (i_sl7nl1arc_sys_sleep_r) // <   npu_top
  , .sl7nl1arc_sys_sleep_mode_r    (i_sl7nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl7nl1arc_sys_halt_r          (i_sl7nl1arc_sys_halt_r) // <   npu_top
  , .sl7nl1arc_sys_tf_halt_r       (i_sl7nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl8nl1arc_arc_halt_ack_a      (i_sl8nl1arc_arc_halt_ack) // <   npu_top
  , .sl8nl1arc_ext_arc_halt_req_a  (sl8nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl8nl1arc_arc_run_ack_a       (i_sl8nl1arc_arc_run_ack) // <   npu_top
  , .sl8nl1arc_ext_arc_run_req_a   (sl8nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl8nl1arc_sys_sleep_r         (i_sl8nl1arc_sys_sleep_r) // <   npu_top
  , .sl8nl1arc_sys_sleep_mode_r    (i_sl8nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl8nl1arc_sys_halt_r          (i_sl8nl1arc_sys_halt_r) // <   npu_top
  , .sl8nl1arc_sys_tf_halt_r       (i_sl8nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl9nl1arc_arc_halt_ack_a      (i_sl9nl1arc_arc_halt_ack) // <   npu_top
  , .sl9nl1arc_ext_arc_halt_req_a  (sl9nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl9nl1arc_arc_run_ack_a       (i_sl9nl1arc_arc_run_ack) // <   npu_top
  , .sl9nl1arc_ext_arc_run_req_a   (sl9nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl9nl1arc_sys_sleep_r         (i_sl9nl1arc_sys_sleep_r) // <   npu_top
  , .sl9nl1arc_sys_sleep_mode_r    (i_sl9nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl9nl1arc_sys_halt_r          (i_sl9nl1arc_sys_halt_r) // <   npu_top
  , .sl9nl1arc_sys_tf_halt_r       (i_sl9nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl10nl1arc_arc_halt_ack_a     (i_sl10nl1arc_arc_halt_ack) // <   npu_top
  , .sl10nl1arc_ext_arc_halt_req_a (sl10nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl10nl1arc_arc_run_ack_a      (i_sl10nl1arc_arc_run_ack) // <   npu_top
  , .sl10nl1arc_ext_arc_run_req_a  (sl10nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl10nl1arc_sys_sleep_r        (i_sl10nl1arc_sys_sleep_r) // <   npu_top
  , .sl10nl1arc_sys_sleep_mode_r   (i_sl10nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl10nl1arc_sys_halt_r         (i_sl10nl1arc_sys_halt_r) // <   npu_top
  , .sl10nl1arc_sys_tf_halt_r      (i_sl10nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl11nl1arc_arc_halt_ack_a     (i_sl11nl1arc_arc_halt_ack) // <   npu_top
  , .sl11nl1arc_ext_arc_halt_req_a (sl11nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl11nl1arc_arc_run_ack_a      (i_sl11nl1arc_arc_run_ack) // <   npu_top
  , .sl11nl1arc_ext_arc_run_req_a  (sl11nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl11nl1arc_sys_sleep_r        (i_sl11nl1arc_sys_sleep_r) // <   npu_top
  , .sl11nl1arc_sys_sleep_mode_r   (i_sl11nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl11nl1arc_sys_halt_r         (i_sl11nl1arc_sys_halt_r) // <   npu_top
  , .sl11nl1arc_sys_tf_halt_r      (i_sl11nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl12nl1arc_arc_halt_ack_a     (i_sl12nl1arc_arc_halt_ack) // <   npu_top
  , .sl12nl1arc_ext_arc_halt_req_a (sl12nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl12nl1arc_arc_run_ack_a      (i_sl12nl1arc_arc_run_ack) // <   npu_top
  , .sl12nl1arc_ext_arc_run_req_a  (sl12nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl12nl1arc_sys_sleep_r        (i_sl12nl1arc_sys_sleep_r) // <   npu_top
  , .sl12nl1arc_sys_sleep_mode_r   (i_sl12nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl12nl1arc_sys_halt_r         (i_sl12nl1arc_sys_halt_r) // <   npu_top
  , .sl12nl1arc_sys_tf_halt_r      (i_sl12nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl13nl1arc_arc_halt_ack_a     (i_sl13nl1arc_arc_halt_ack) // <   npu_top
  , .sl13nl1arc_ext_arc_halt_req_a (sl13nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl13nl1arc_arc_run_ack_a      (i_sl13nl1arc_arc_run_ack) // <   npu_top
  , .sl13nl1arc_ext_arc_run_req_a  (sl13nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl13nl1arc_sys_sleep_r        (i_sl13nl1arc_sys_sleep_r) // <   npu_top
  , .sl13nl1arc_sys_sleep_mode_r   (i_sl13nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl13nl1arc_sys_halt_r         (i_sl13nl1arc_sys_halt_r) // <   npu_top
  , .sl13nl1arc_sys_tf_halt_r      (i_sl13nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl14nl1arc_arc_halt_ack_a     (i_sl14nl1arc_arc_halt_ack) // <   npu_top
  , .sl14nl1arc_ext_arc_halt_req_a (sl14nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl14nl1arc_arc_run_ack_a      (i_sl14nl1arc_arc_run_ack) // <   npu_top
  , .sl14nl1arc_ext_arc_run_req_a  (sl14nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl14nl1arc_sys_sleep_r        (i_sl14nl1arc_sys_sleep_r) // <   npu_top
  , .sl14nl1arc_sys_sleep_mode_r   (i_sl14nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl14nl1arc_sys_halt_r         (i_sl14nl1arc_sys_halt_r) // <   npu_top
  , .sl14nl1arc_sys_tf_halt_r      (i_sl14nl1arc_sys_tf_halt_r) // <   npu_top
  , .sl15nl1arc_arc_halt_ack_a     (i_sl15nl1arc_arc_halt_ack) // <   npu_top
  , .sl15nl1arc_ext_arc_halt_req_a (sl15nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl15nl1arc_arc_run_ack_a      (i_sl15nl1arc_arc_run_ack) // <   npu_top
  , .sl15nl1arc_ext_arc_run_req_a  (sl15nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl15nl1arc_sys_sleep_r        (i_sl15nl1arc_sys_sleep_r) // <   npu_top
  , .sl15nl1arc_sys_sleep_mode_r   (i_sl15nl1arc_sys_sleep_mode_r) // <   npu_top
  , .sl15nl1arc_sys_halt_r         (i_sl15nl1arc_sys_halt_r) // <   npu_top
  , .sl15nl1arc_sys_tf_halt_r      (i_sl15nl1arc_sys_tf_halt_r) // <   npu_top
  , .v0c0arc_halt_ack_a            (v0c0arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c0ext_arc_halt_req_a        (v0c0ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c0arc_run_ack_a             (v0c0arc_run_ack_a) // <   arcsync_top_stub
  , .v0c0ext_arc_run_req_a         (v0c0ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c0sys_sleep_r               (v0c0sys_sleep_r) // <   arcsync_top_stub
  , .v0c0sys_sleep_mode_r          (v0c0sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c0sys_halt_r                (v0c0sys_halt_r) // <   arcsync_top_stub
  , .v0c0sys_tf_halt_r             (v0c0sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c0pmode                     (v0c0pmode)     // <   arcsync_top_stub
  , .v0c1arc_halt_ack_a            (v0c1arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c1ext_arc_halt_req_a        (v0c1ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c1arc_run_ack_a             (v0c1arc_run_ack_a) // <   arcsync_top_stub
  , .v0c1ext_arc_run_req_a         (v0c1ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c1sys_sleep_r               (v0c1sys_sleep_r) // <   arcsync_top_stub
  , .v0c1sys_sleep_mode_r          (v0c1sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c1sys_halt_r                (v0c1sys_halt_r) // <   arcsync_top_stub
  , .v0c1sys_tf_halt_r             (v0c1sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c1pmode                     (v0c1pmode)     // <   arcsync_top_stub
  , .v0c2arc_halt_ack_a            (v0c2arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c2ext_arc_halt_req_a        (v0c2ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c2arc_run_ack_a             (v0c2arc_run_ack_a) // <   arcsync_top_stub
  , .v0c2ext_arc_run_req_a         (v0c2ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c2sys_sleep_r               (v0c2sys_sleep_r) // <   arcsync_top_stub
  , .v0c2sys_sleep_mode_r          (v0c2sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c2sys_halt_r                (v0c2sys_halt_r) // <   arcsync_top_stub
  , .v0c2sys_tf_halt_r             (v0c2sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c2pmode                     (v0c2pmode)     // <   arcsync_top_stub
  , .v0c3arc_halt_ack_a            (v0c3arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c3ext_arc_halt_req_a        (v0c3ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c3arc_run_ack_a             (v0c3arc_run_ack_a) // <   arcsync_top_stub
  , .v0c3ext_arc_run_req_a         (v0c3ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c3sys_sleep_r               (v0c3sys_sleep_r) // <   arcsync_top_stub
  , .v0c3sys_sleep_mode_r          (v0c3sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c3sys_halt_r                (v0c3sys_halt_r) // <   arcsync_top_stub
  , .v0c3sys_tf_halt_r             (v0c3sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c3pmode                     (v0c3pmode)     // <   arcsync_top_stub
  , .arcsync_axi_clk               (arcsync_axi_clk) // <   outside-of-hierarchy
  , .arcsync_axi_rst_a             (arcsync_axi_rst_a) // <   outside-of-hierarchy
  , .arcsync_core_iso_override     (arcsync_core_iso_override) // <   outside-of-hierarchy
  , .test_mode                     (test_mode)     // <   outside-of-hierarchy
  , .arcsync_clk                   (arcsync_clk)   // <   outside-of-hierarchy
  , .arcsync_rst_a                 (arcsync_rst_a) // <   outside-of-hierarchy
  , .grp0_rst_a                    (i_grp0_rst_a)  //   > npu_top
  , .grp0_clk_en                   (i_grp0_clk_en) //   > npu_top
  , .grp1_rst_a                    (i_grp1_rst_a)  //   > npu_top
  , .grp1_clk_en                   (i_grp1_clk_en) //   > npu_top
  , .grp2_rst_a                    (i_grp2_rst_a)  //   > npu_top
  , .grp2_clk_en                   (i_grp2_clk_en) //   > npu_top
  , .grp3_rst_a                    (i_grp3_rst_a)  //   > npu_top
  , .grp3_clk_en                   (i_grp3_clk_en) //   > npu_top
  , .sl0_rst_a                     (i_sl0_rst_a)   //   > npu_top
  , .sl0_clk_en                    (i_sl0_clk_en_a) //   > npu_top
  , .sl1_rst_a                     (i_sl1_rst_a)   //   > npu_top
  , .sl1_clk_en                    (i_sl1_clk_en_a) //   > npu_top
  , .sl2_rst_a                     (i_sl2_rst_a)   //   > npu_top
  , .sl2_clk_en                    (i_sl2_clk_en_a) //   > npu_top
  , .sl3_rst_a                     (i_sl3_rst_a)   //   > npu_top
  , .sl3_clk_en                    (i_sl3_clk_en_a) //   > npu_top
  , .sl4_rst_a                     (i_sl4_rst_a)   //   > npu_top
  , .sl4_clk_en                    (i_sl4_clk_en_a) //   > npu_top
  , .sl5_rst_a                     (i_sl5_rst_a)   //   > npu_top
  , .sl5_clk_en                    (i_sl5_clk_en_a) //   > npu_top
  , .sl6_rst_a                     (i_sl6_rst_a)   //   > npu_top
  , .sl6_clk_en                    (i_sl6_clk_en_a) //   > npu_top
  , .sl7_rst_a                     (i_sl7_rst_a)   //   > npu_top
  , .sl7_clk_en                    (i_sl7_clk_en_a) //   > npu_top
  , .sl8_rst_a                     (i_sl8_rst_a)   //   > npu_top
  , .sl8_clk_en                    (i_sl8_clk_en_a) //   > npu_top
  , .sl9_rst_a                     (i_sl9_rst_a)   //   > npu_top
  , .sl9_clk_en                    (i_sl9_clk_en_a) //   > npu_top
  , .sl10_rst_a                    (i_sl10_rst_a)  //   > npu_top
  , .sl10_clk_en                   (i_sl10_clk_en_a) //   > npu_top
  , .sl11_rst_a                    (i_sl11_rst_a)  //   > npu_top
  , .sl11_clk_en                   (i_sl11_clk_en_a) //   > npu_top
  , .sl12_rst_a                    (i_sl12_rst_a)  //   > npu_top
  , .sl12_clk_en                   (i_sl12_clk_en_a) //   > npu_top
  , .sl13_rst_a                    (i_sl13_rst_a)  //   > npu_top
  , .sl13_clk_en                   (i_sl13_clk_en_a) //   > npu_top
  , .sl14_rst_a                    (i_sl14_rst_a)  //   > npu_top
  , .sl14_clk_en                   (i_sl14_clk_en_a) //   > npu_top
  , .sl15_rst_a                    (i_sl15_rst_a)  //   > npu_top
  , .sl15_clk_en                   (i_sl15_clk_en_a) //   > npu_top
  , .nl2arc0_rst_a                 (i_nl2arc0_rst_a) //   > npu_top
  , .nl2arc0_clk_en                (i_nl2arc0_clk_en_a) //   > npu_top
  , .nl2arc1_rst_a                 (i_nl2arc1_rst_a) //   > npu_top
  , .nl2arc1_clk_en                (i_nl2arc1_clk_en_a) //   > npu_top
  , .nl2_rst                       (i_nl2_rst_a)   //   > npu_top
  , .nl2arc_pwr_dwn                (i_nl2arc_pwr_dwn) //   > npu_top
  , .nl2arc0_pwr_dwn               (i_nl2arc0_pwr_dwn) //   > npu_top
  , .nl2arc1_pwr_dwn               (i_nl2arc1_pwr_dwn) //   > npu_top
  , .grp0_pwr_dwn                  (i_grp0_pwr_dwn) //   > npu_top
  , .grp1_pwr_dwn                  (i_grp1_pwr_dwn) //   > npu_top
  , .grp2_pwr_dwn                  (i_grp2_pwr_dwn) //   > npu_top
  , .grp3_pwr_dwn                  (i_grp3_pwr_dwn) //   > npu_top
  , .sl0nl1arc_pwr_dwn             (i_sl0nl1arc_pwr_dwn) //   > npu_top
  , .sl1nl1arc_pwr_dwn             (i_sl1nl1arc_pwr_dwn) //   > npu_top
  , .sl2nl1arc_pwr_dwn             (i_sl2nl1arc_pwr_dwn) //   > npu_top
  , .sl3nl1arc_pwr_dwn             (i_sl3nl1arc_pwr_dwn) //   > npu_top
  , .sl4nl1arc_pwr_dwn             (i_sl4nl1arc_pwr_dwn) //   > npu_top
  , .sl5nl1arc_pwr_dwn             (i_sl5nl1arc_pwr_dwn) //   > npu_top
  , .sl6nl1arc_pwr_dwn             (i_sl6nl1arc_pwr_dwn) //   > npu_top
  , .sl7nl1arc_pwr_dwn             (i_sl7nl1arc_pwr_dwn) //   > npu_top
  , .sl8nl1arc_pwr_dwn             (i_sl8nl1arc_pwr_dwn) //   > npu_top
  , .sl9nl1arc_pwr_dwn             (i_sl9nl1arc_pwr_dwn) //   > npu_top
  , .sl10nl1arc_pwr_dwn            (i_sl10nl1arc_pwr_dwn) //   > npu_top
  , .sl11nl1arc_pwr_dwn            (i_sl11nl1arc_pwr_dwn) //   > npu_top
  , .sl12nl1arc_pwr_dwn            (i_sl12nl1arc_pwr_dwn) //   > npu_top
  , .sl13nl1arc_pwr_dwn            (i_sl13nl1arc_pwr_dwn) //   > npu_top
  , .sl14nl1arc_pwr_dwn            (i_sl14nl1arc_pwr_dwn) //   > npu_top
  , .sl15nl1arc_pwr_dwn            (i_sl15nl1arc_pwr_dwn) //   > npu_top
  , .nl2arc_isolate_n              (i_nl2arc_isolate_n) //   > npu_top
  , .nl2arc_isolate                (i_nl2arc_isolate) //   > npu_top
  , .nl2arc_pd_mem                 (i_nl2arc_pd_mem) //   > npu_top
  , .nl2arc_pd_logic               (i_nl2arc_pd_logic) //   > npu_top
  , .grp0_isolate_n                (i_grp0_isolate_n) //   > npu_top
  , .grp0_isolate                  (i_grp0_isolate) //   > npu_top
  , .grp0_pd_mem                   (i_grp0_pd_mem) //   > npu_top
  , .grp0_pd_logic                 (i_grp0_pd_logic) //   > npu_top
  , .grp1_isolate_n                (i_grp1_isolate_n) //   > npu_top
  , .grp1_isolate                  (i_grp1_isolate) //   > npu_top
  , .grp1_pd_mem                   (i_grp1_pd_mem) //   > npu_top
  , .grp1_pd_logic                 (i_grp1_pd_logic) //   > npu_top
  , .grp2_isolate_n                (i_grp2_isolate_n) //   > npu_top
  , .grp2_isolate                  (i_grp2_isolate) //   > npu_top
  , .grp2_pd_mem                   (i_grp2_pd_mem) //   > npu_top
  , .grp2_pd_logic                 (i_grp2_pd_logic) //   > npu_top
  , .grp3_isolate_n                (i_grp3_isolate_n) //   > npu_top
  , .grp3_isolate                  (i_grp3_isolate) //   > npu_top
  , .grp3_pd_mem                   (i_grp3_pd_mem) //   > npu_top
  , .grp3_pd_logic                 (i_grp3_pd_logic) //   > npu_top
  , .sl0nl1arc_isolate_n           (i_sl0nl1arc_isolate_n) //   > npu_top
  , .sl0nl1arc_isolate             (i_sl0nl1arc_isolate) //   > npu_top
  , .sl0nl1arc_pd_mem              (i_sl0nl1arc_pd_mem) //   > npu_top
  , .sl0nl1arc_pd_logic            (i_sl0nl1arc_pd_logic) //   > npu_top
  , .sl1nl1arc_isolate_n           (i_sl1nl1arc_isolate_n) //   > npu_top
  , .sl1nl1arc_isolate             (i_sl1nl1arc_isolate) //   > npu_top
  , .sl1nl1arc_pd_mem              (i_sl1nl1arc_pd_mem) //   > npu_top
  , .sl1nl1arc_pd_logic            (i_sl1nl1arc_pd_logic) //   > npu_top
  , .sl2nl1arc_isolate_n           (i_sl2nl1arc_isolate_n) //   > npu_top
  , .sl2nl1arc_isolate             (i_sl2nl1arc_isolate) //   > npu_top
  , .sl2nl1arc_pd_mem              (i_sl2nl1arc_pd_mem) //   > npu_top
  , .sl2nl1arc_pd_logic            (i_sl2nl1arc_pd_logic) //   > npu_top
  , .sl3nl1arc_isolate_n           (i_sl3nl1arc_isolate_n) //   > npu_top
  , .sl3nl1arc_isolate             (i_sl3nl1arc_isolate) //   > npu_top
  , .sl3nl1arc_pd_mem              (i_sl3nl1arc_pd_mem) //   > npu_top
  , .sl3nl1arc_pd_logic            (i_sl3nl1arc_pd_logic) //   > npu_top
  , .sl4nl1arc_isolate_n           (i_sl4nl1arc_isolate_n) //   > npu_top
  , .sl4nl1arc_isolate             (i_sl4nl1arc_isolate) //   > npu_top
  , .sl4nl1arc_pd_mem              (i_sl4nl1arc_pd_mem) //   > npu_top
  , .sl4nl1arc_pd_logic            (i_sl4nl1arc_pd_logic) //   > npu_top
  , .sl5nl1arc_isolate_n           (i_sl5nl1arc_isolate_n) //   > npu_top
  , .sl5nl1arc_isolate             (i_sl5nl1arc_isolate) //   > npu_top
  , .sl5nl1arc_pd_mem              (i_sl5nl1arc_pd_mem) //   > npu_top
  , .sl5nl1arc_pd_logic            (i_sl5nl1arc_pd_logic) //   > npu_top
  , .sl6nl1arc_isolate_n           (i_sl6nl1arc_isolate_n) //   > npu_top
  , .sl6nl1arc_isolate             (i_sl6nl1arc_isolate) //   > npu_top
  , .sl6nl1arc_pd_mem              (i_sl6nl1arc_pd_mem) //   > npu_top
  , .sl6nl1arc_pd_logic            (i_sl6nl1arc_pd_logic) //   > npu_top
  , .sl7nl1arc_isolate_n           (i_sl7nl1arc_isolate_n) //   > npu_top
  , .sl7nl1arc_isolate             (i_sl7nl1arc_isolate) //   > npu_top
  , .sl7nl1arc_pd_mem              (i_sl7nl1arc_pd_mem) //   > npu_top
  , .sl7nl1arc_pd_logic            (i_sl7nl1arc_pd_logic) //   > npu_top
  , .sl8nl1arc_isolate_n           (i_sl8nl1arc_isolate_n) //   > npu_top
  , .sl8nl1arc_isolate             (i_sl8nl1arc_isolate) //   > npu_top
  , .sl8nl1arc_pd_mem              (i_sl8nl1arc_pd_mem) //   > npu_top
  , .sl8nl1arc_pd_logic            (i_sl8nl1arc_pd_logic) //   > npu_top
  , .sl9nl1arc_isolate_n           (i_sl9nl1arc_isolate_n) //   > npu_top
  , .sl9nl1arc_isolate             (i_sl9nl1arc_isolate) //   > npu_top
  , .sl9nl1arc_pd_mem              (i_sl9nl1arc_pd_mem) //   > npu_top
  , .sl9nl1arc_pd_logic            (i_sl9nl1arc_pd_logic) //   > npu_top
  , .sl10nl1arc_isolate_n          (i_sl10nl1arc_isolate_n) //   > npu_top
  , .sl10nl1arc_isolate            (i_sl10nl1arc_isolate) //   > npu_top
  , .sl10nl1arc_pd_mem             (i_sl10nl1arc_pd_mem) //   > npu_top
  , .sl10nl1arc_pd_logic           (i_sl10nl1arc_pd_logic) //   > npu_top
  , .sl11nl1arc_isolate_n          (i_sl11nl1arc_isolate_n) //   > npu_top
  , .sl11nl1arc_isolate            (i_sl11nl1arc_isolate) //   > npu_top
  , .sl11nl1arc_pd_mem             (i_sl11nl1arc_pd_mem) //   > npu_top
  , .sl11nl1arc_pd_logic           (i_sl11nl1arc_pd_logic) //   > npu_top
  , .sl12nl1arc_isolate_n          (i_sl12nl1arc_isolate_n) //   > npu_top
  , .sl12nl1arc_isolate            (i_sl12nl1arc_isolate) //   > npu_top
  , .sl12nl1arc_pd_mem             (i_sl12nl1arc_pd_mem) //   > npu_top
  , .sl12nl1arc_pd_logic           (i_sl12nl1arc_pd_logic) //   > npu_top
  , .sl13nl1arc_isolate_n          (i_sl13nl1arc_isolate_n) //   > npu_top
  , .sl13nl1arc_isolate            (i_sl13nl1arc_isolate) //   > npu_top
  , .sl13nl1arc_pd_mem             (i_sl13nl1arc_pd_mem) //   > npu_top
  , .sl13nl1arc_pd_logic           (i_sl13nl1arc_pd_logic) //   > npu_top
  , .sl14nl1arc_isolate_n          (i_sl14nl1arc_isolate_n) //   > npu_top
  , .sl14nl1arc_isolate            (i_sl14nl1arc_isolate) //   > npu_top
  , .sl14nl1arc_pd_mem             (i_sl14nl1arc_pd_mem) //   > npu_top
  , .sl14nl1arc_pd_logic           (i_sl14nl1arc_pd_logic) //   > npu_top
  , .sl15nl1arc_isolate_n          (i_sl15nl1arc_isolate_n) //   > npu_top
  , .sl15nl1arc_isolate            (i_sl15nl1arc_isolate) //   > npu_top
  , .sl15nl1arc_pd_mem             (i_sl15nl1arc_pd_mem) //   > npu_top
  , .sl15nl1arc_pd_logic           (i_sl15nl1arc_pd_logic) //   > npu_top
  , .nl2arc0_intvbase              (i_nl2arc0_intvbase_in) //   > npu_top
  , .nl2arc0_arc_halt_req          (i_nl2arc0_arc_halt_req) //   > npu_top
  , .nl2arc0_arc_run_req           (i_nl2arc0_arc_run_req) //   > npu_top
  , .nl2arc0_arc_irq_a             (i_nl2arc0_arc_irq_a) //   > npu_top
  , .nl2arc0_arc_event_a           (i_nl2arc0_arc_event_a) //   > npu_top
  , .nl2arc1_intvbase              (i_nl2arc1_intvbase_in) //   > npu_top
  , .nl2arc1_arc_halt_req          (i_nl2arc1_arc_halt_req) //   > npu_top
  , .nl2arc1_arc_run_req           (i_nl2arc1_arc_run_req) //   > npu_top
  , .nl2arc1_arc_irq_a             (i_nl2arc1_arc_irq_a) //   > npu_top
  , .nl2arc1_arc_event_a           (i_nl2arc1_arc_event_a) //   > npu_top
  , .sl0nl1arc_intvbase            (i_sl0nl1arc_intvbase_in) //   > npu_top
  , .sl0nl1arc_arc_halt_req        (i_sl0nl1arc_arc_halt_req) //   > npu_top
  , .sl0nl1arc_arc_run_req         (i_sl0nl1arc_arc_run_req) //   > npu_top
  , .sl0nl1arc_arc_irq             (i_sl0nl1arc_arc_irq_a) //   > npu_top
  , .sl1nl1arc_intvbase            (i_sl1nl1arc_intvbase_in) //   > npu_top
  , .sl1nl1arc_arc_halt_req        (i_sl1nl1arc_arc_halt_req) //   > npu_top
  , .sl1nl1arc_arc_run_req         (i_sl1nl1arc_arc_run_req) //   > npu_top
  , .sl1nl1arc_arc_irq             (i_sl1nl1arc_arc_irq_a) //   > npu_top
  , .sl2nl1arc_intvbase            (i_sl2nl1arc_intvbase_in) //   > npu_top
  , .sl2nl1arc_arc_halt_req        (i_sl2nl1arc_arc_halt_req) //   > npu_top
  , .sl2nl1arc_arc_run_req         (i_sl2nl1arc_arc_run_req) //   > npu_top
  , .sl2nl1arc_arc_irq             (i_sl2nl1arc_arc_irq_a) //   > npu_top
  , .sl3nl1arc_intvbase            (i_sl3nl1arc_intvbase_in) //   > npu_top
  , .sl3nl1arc_arc_halt_req        (i_sl3nl1arc_arc_halt_req) //   > npu_top
  , .sl3nl1arc_arc_run_req         (i_sl3nl1arc_arc_run_req) //   > npu_top
  , .sl3nl1arc_arc_irq             (i_sl3nl1arc_arc_irq_a) //   > npu_top
  , .sl4nl1arc_intvbase            (i_sl4nl1arc_intvbase_in) //   > npu_top
  , .sl4nl1arc_arc_halt_req        (i_sl4nl1arc_arc_halt_req) //   > npu_top
  , .sl4nl1arc_arc_run_req         (i_sl4nl1arc_arc_run_req) //   > npu_top
  , .sl4nl1arc_arc_irq             (i_sl4nl1arc_arc_irq_a) //   > npu_top
  , .sl5nl1arc_intvbase            (i_sl5nl1arc_intvbase_in) //   > npu_top
  , .sl5nl1arc_arc_halt_req        (i_sl5nl1arc_arc_halt_req) //   > npu_top
  , .sl5nl1arc_arc_run_req         (i_sl5nl1arc_arc_run_req) //   > npu_top
  , .sl5nl1arc_arc_irq             (i_sl5nl1arc_arc_irq_a) //   > npu_top
  , .sl6nl1arc_intvbase            (i_sl6nl1arc_intvbase_in) //   > npu_top
  , .sl6nl1arc_arc_halt_req        (i_sl6nl1arc_arc_halt_req) //   > npu_top
  , .sl6nl1arc_arc_run_req         (i_sl6nl1arc_arc_run_req) //   > npu_top
  , .sl6nl1arc_arc_irq             (i_sl6nl1arc_arc_irq_a) //   > npu_top
  , .sl7nl1arc_intvbase            (i_sl7nl1arc_intvbase_in) //   > npu_top
  , .sl7nl1arc_arc_halt_req        (i_sl7nl1arc_arc_halt_req) //   > npu_top
  , .sl7nl1arc_arc_run_req         (i_sl7nl1arc_arc_run_req) //   > npu_top
  , .sl7nl1arc_arc_irq             (i_sl7nl1arc_arc_irq_a) //   > npu_top
  , .sl8nl1arc_intvbase            (i_sl8nl1arc_intvbase_in) //   > npu_top
  , .sl8nl1arc_arc_halt_req        (i_sl8nl1arc_arc_halt_req) //   > npu_top
  , .sl8nl1arc_arc_run_req         (i_sl8nl1arc_arc_run_req) //   > npu_top
  , .sl8nl1arc_arc_irq             (i_sl8nl1arc_arc_irq_a) //   > npu_top
  , .sl9nl1arc_intvbase            (i_sl9nl1arc_intvbase_in) //   > npu_top
  , .sl9nl1arc_arc_halt_req        (i_sl9nl1arc_arc_halt_req) //   > npu_top
  , .sl9nl1arc_arc_run_req         (i_sl9nl1arc_arc_run_req) //   > npu_top
  , .sl9nl1arc_arc_irq             (i_sl9nl1arc_arc_irq_a) //   > npu_top
  , .sl10nl1arc_intvbase           (i_sl10nl1arc_intvbase_in) //   > npu_top
  , .sl10nl1arc_arc_halt_req       (i_sl10nl1arc_arc_halt_req) //   > npu_top
  , .sl10nl1arc_arc_run_req        (i_sl10nl1arc_arc_run_req) //   > npu_top
  , .sl10nl1arc_arc_irq            (i_sl10nl1arc_arc_irq_a) //   > npu_top
  , .sl11nl1arc_intvbase           (i_sl11nl1arc_intvbase_in) //   > npu_top
  , .sl11nl1arc_arc_halt_req       (i_sl11nl1arc_arc_halt_req) //   > npu_top
  , .sl11nl1arc_arc_run_req        (i_sl11nl1arc_arc_run_req) //   > npu_top
  , .sl11nl1arc_arc_irq            (i_sl11nl1arc_arc_irq_a) //   > npu_top
  , .sl12nl1arc_intvbase           (i_sl12nl1arc_intvbase_in) //   > npu_top
  , .sl12nl1arc_arc_halt_req       (i_sl12nl1arc_arc_halt_req) //   > npu_top
  , .sl12nl1arc_arc_run_req        (i_sl12nl1arc_arc_run_req) //   > npu_top
  , .sl12nl1arc_arc_irq            (i_sl12nl1arc_arc_irq_a) //   > npu_top
  , .sl13nl1arc_intvbase           (i_sl13nl1arc_intvbase_in) //   > npu_top
  , .sl13nl1arc_arc_halt_req       (i_sl13nl1arc_arc_halt_req) //   > npu_top
  , .sl13nl1arc_arc_run_req        (i_sl13nl1arc_arc_run_req) //   > npu_top
  , .sl13nl1arc_arc_irq            (i_sl13nl1arc_arc_irq_a) //   > npu_top
  , .sl14nl1arc_intvbase           (i_sl14nl1arc_intvbase_in) //   > npu_top
  , .sl14nl1arc_arc_halt_req       (i_sl14nl1arc_arc_halt_req) //   > npu_top
  , .sl14nl1arc_arc_run_req        (i_sl14nl1arc_arc_run_req) //   > npu_top
  , .sl14nl1arc_arc_irq            (i_sl14nl1arc_arc_irq_a) //   > npu_top
  , .sl15nl1arc_intvbase           (i_sl15nl1arc_intvbase_in) //   > npu_top
  , .sl15nl1arc_arc_halt_req       (i_sl15nl1arc_arc_halt_req) //   > npu_top
  , .sl15nl1arc_arc_run_req        (i_sl15nl1arc_arc_run_req) //   > npu_top
  , .sl15nl1arc_arc_irq            (i_sl15nl1arc_arc_irq_a) //   > npu_top
  , .nl2arc_clusternum             (i_nl2arc0_clusternum) //   > npu_top
  , .v0c0_pwr_dwn                  (i_v0c0_pwr_dwn) //   > unconnected
  , .v0c1_pwr_dwn                  (i_v0c1_pwr_dwn) //   > unconnected
  , .v0c2_pwr_dwn                  (i_v0c2_pwr_dwn) //   > unconnected
  , .v0c3_pwr_dwn                  (i_v0c3_pwr_dwn) //   > unconnected
  , .nl2arc_pd_logic1              (nl2arc_pd_logic1) //   > arcsync_top_stub
  , .nl2arc_pd_logic2              (nl2arc_pd_logic2) //   > arcsync_top_stub
  , .grp0_pd_logic1                (grp0_pd_logic1) //   > arcsync_top_stub
  , .grp0_pd_logic2                (grp0_pd_logic2) //   > arcsync_top_stub
  , .grp1_pd_logic1                (grp1_pd_logic1) //   > arcsync_top_stub
  , .grp1_pd_logic2                (grp1_pd_logic2) //   > arcsync_top_stub
  , .grp2_pd_logic1                (grp2_pd_logic1) //   > arcsync_top_stub
  , .grp2_pd_logic2                (grp2_pd_logic2) //   > arcsync_top_stub
  , .grp3_pd_logic1                (grp3_pd_logic1) //   > arcsync_top_stub
  , .grp3_pd_logic2                (grp3_pd_logic2) //   > arcsync_top_stub
  , .sl0nl1arc_pd_logic1           (sl0nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl0nl1arc_pd_logic2           (sl0nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl1nl1arc_pd_logic1           (sl1nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl1nl1arc_pd_logic2           (sl1nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl2nl1arc_pd_logic1           (sl2nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl2nl1arc_pd_logic2           (sl2nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl3nl1arc_pd_logic1           (sl3nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl3nl1arc_pd_logic2           (sl3nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl4nl1arc_pd_logic1           (sl4nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl4nl1arc_pd_logic2           (sl4nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl5nl1arc_pd_logic1           (sl5nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl5nl1arc_pd_logic2           (sl5nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl6nl1arc_pd_logic1           (sl6nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl6nl1arc_pd_logic2           (sl6nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl7nl1arc_pd_logic1           (sl7nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl7nl1arc_pd_logic2           (sl7nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl8nl1arc_pd_logic1           (sl8nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl8nl1arc_pd_logic2           (sl8nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl9nl1arc_pd_logic1           (sl9nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl9nl1arc_pd_logic2           (sl9nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl10nl1arc_pd_logic1          (sl10nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl10nl1arc_pd_logic2          (sl10nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl11nl1arc_pd_logic1          (sl11nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl11nl1arc_pd_logic2          (sl11nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl12nl1arc_pd_logic1          (sl12nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl12nl1arc_pd_logic2          (sl12nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl13nl1arc_pd_logic1          (sl13nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl13nl1arc_pd_logic2          (sl13nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl14nl1arc_pd_logic1          (sl14nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl14nl1arc_pd_logic2          (sl14nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl15nl1arc_pd_logic1          (sl15nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl15nl1arc_pd_logic2          (sl15nl1arc_pd_logic2) //   > arcsync_top_stub
  , .v0csm_addr_base               (v0csm_addr_base) //   > arcsync_top_stub
  , .v0periph_addr_base            (v0periph_addr_base) //   > arcsync_top_stub
  , .v0clusternum                  (v0clusternum)  //   > arcsync_top_stub
  , .v0c0arcnum                    (v0c0arcnum)    //   > arcsync_top_stub
  , .v0c0intvbase                  (v0c0intvbase)  //   > arcsync_top_stub
  , .v0c0rst_a                     (v0c0rst_a)     //   > arcsync_top_stub
  , .v0c0clk_en                    (v0c0clk_en)    //   > arcsync_top_stub
  , .v0c0arc_halt_req              (v0c0arc_halt_req) //   > arcsync_top_stub
  , .v0c0ext_arc_halt_ack          (v0c0ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c0arc_run_req               (v0c0arc_run_req) //   > arcsync_top_stub
  , .v0c0ext_arc_run_ack           (v0c0ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c0arc_irq0_a                (v0c0arc_irq0_a) //   > arcsync_top_stub
  , .v0c0arc_irq1_a                (v0c0arc_irq1_a) //   > arcsync_top_stub
  , .v0c0arc_event0_a              (v0c0arc_event0_a) //   > arcsync_top_stub
  , .v0c0arc_event1_a              (v0c0arc_event1_a) //   > arcsync_top_stub
  , .v0c1arcnum                    (v0c1arcnum)    //   > arcsync_top_stub
  , .v0c1intvbase                  (v0c1intvbase)  //   > arcsync_top_stub
  , .v0c1rst_a                     (v0c1rst_a)     //   > arcsync_top_stub
  , .v0c1clk_en                    (v0c1clk_en)    //   > arcsync_top_stub
  , .v0c1arc_halt_req              (v0c1arc_halt_req) //   > arcsync_top_stub
  , .v0c1ext_arc_halt_ack          (v0c1ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c1arc_run_req               (v0c1arc_run_req) //   > arcsync_top_stub
  , .v0c1ext_arc_run_ack           (v0c1ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c1arc_irq0_a                (v0c1arc_irq0_a) //   > arcsync_top_stub
  , .v0c1arc_irq1_a                (v0c1arc_irq1_a) //   > arcsync_top_stub
  , .v0c1arc_event0_a              (v0c1arc_event0_a) //   > arcsync_top_stub
  , .v0c1arc_event1_a              (v0c1arc_event1_a) //   > arcsync_top_stub
  , .v0c2arcnum                    (v0c2arcnum)    //   > arcsync_top_stub
  , .v0c2intvbase                  (v0c2intvbase)  //   > arcsync_top_stub
  , .v0c2rst_a                     (v0c2rst_a)     //   > arcsync_top_stub
  , .v0c2clk_en                    (v0c2clk_en)    //   > arcsync_top_stub
  , .v0c2arc_halt_req              (v0c2arc_halt_req) //   > arcsync_top_stub
  , .v0c2ext_arc_halt_ack          (v0c2ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c2arc_run_req               (v0c2arc_run_req) //   > arcsync_top_stub
  , .v0c2ext_arc_run_ack           (v0c2ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c2arc_irq0_a                (v0c2arc_irq0_a) //   > arcsync_top_stub
  , .v0c2arc_irq1_a                (v0c2arc_irq1_a) //   > arcsync_top_stub
  , .v0c2arc_event0_a              (v0c2arc_event0_a) //   > arcsync_top_stub
  , .v0c2arc_event1_a              (v0c2arc_event1_a) //   > arcsync_top_stub
  , .v0c3arcnum                    (v0c3arcnum)    //   > arcsync_top_stub
  , .v0c3intvbase                  (v0c3intvbase)  //   > arcsync_top_stub
  , .v0c3rst_a                     (v0c3rst_a)     //   > arcsync_top_stub
  , .v0c3clk_en                    (v0c3clk_en)    //   > arcsync_top_stub
  , .v0c3arc_halt_req              (v0c3arc_halt_req) //   > arcsync_top_stub
  , .v0c3ext_arc_halt_ack          (v0c3ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c3arc_run_req               (v0c3arc_run_req) //   > arcsync_top_stub
  , .v0c3ext_arc_run_ack           (v0c3ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c3arc_irq0_a                (v0c3arc_irq0_a) //   > arcsync_top_stub
  , .v0c3arc_irq1_a                (v0c3arc_irq1_a) //   > arcsync_top_stub
  , .v0c3arc_event0_a              (v0c3arc_event0_a) //   > arcsync_top_stub
  , .v0c3arc_event1_a              (v0c3arc_event1_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_irq0_a             (vpx_v0_vm0_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_irq_ac_a           (vpx_v0_vm0_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_evt0_a             (vpx_v0_vm0_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_evt_ac_a           (vpx_v0_vm0_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_irq0_a             (vpx_v0_vm1_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_irq_ac_a           (vpx_v0_vm1_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_evt0_a             (vpx_v0_vm1_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_evt_ac_a           (vpx_v0_vm1_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_irq0_a             (vpx_v0_vm2_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_irq_ac_a           (vpx_v0_vm2_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_evt0_a             (vpx_v0_vm2_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_evt_ac_a           (vpx_v0_vm2_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_irq0_a             (vpx_v0_vm3_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_irq_ac_a           (vpx_v0_vm3_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_evt0_a             (vpx_v0_vm3_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_evt_ac_a           (vpx_v0_vm3_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_irq0_a             (vpx_v0_vm4_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_irq_ac_a           (vpx_v0_vm4_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_evt0_a             (vpx_v0_vm4_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_evt_ac_a           (vpx_v0_vm4_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_irq0_a             (vpx_v0_vm5_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_irq_ac_a           (vpx_v0_vm5_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_evt0_a             (vpx_v0_vm5_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_evt_ac_a           (vpx_v0_vm5_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_irq0_a             (vpx_v0_vm6_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_irq_ac_a           (vpx_v0_vm6_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_evt0_a             (vpx_v0_vm6_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_evt_ac_a           (vpx_v0_vm6_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_irq0_a             (vpx_v0_vm7_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_irq_ac_a           (vpx_v0_vm7_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_evt0_a             (vpx_v0_vm7_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_evt_ac_a           (vpx_v0_vm7_evt_ac_a) //   > arcsync_top_stub
  , .v0c0_isolate_n                (v0c0_isolate_n) //   > arcsync_top_stub
  , .v0c0_isolate                  (v0c0_isolate)  //   > arcsync_top_stub
  , .v0c0_pd_mem                   (v0c0_pd_mem)   //   > arcsync_top_stub
  , .v0c0_pd_logic                 (v0c0_pd_logic) //   > arcsync_top_stub
  , .v0c0_pd_logic1                (v0c0_pd_logic1) //   > arcsync_top_stub
  , .v0c0_pd_logic2                (v0c0_pd_logic2) //   > arcsync_top_stub
  , .v0c1_isolate_n                (v0c1_isolate_n) //   > arcsync_top_stub
  , .v0c1_isolate                  (v0c1_isolate)  //   > arcsync_top_stub
  , .v0c1_pd_mem                   (v0c1_pd_mem)   //   > arcsync_top_stub
  , .v0c1_pd_logic                 (v0c1_pd_logic) //   > arcsync_top_stub
  , .v0c1_pd_logic1                (v0c1_pd_logic1) //   > arcsync_top_stub
  , .v0c1_pd_logic2                (v0c1_pd_logic2) //   > arcsync_top_stub
  , .v0c2_isolate_n                (v0c2_isolate_n) //   > arcsync_top_stub
  , .v0c2_isolate                  (v0c2_isolate)  //   > arcsync_top_stub
  , .v0c2_pd_mem                   (v0c2_pd_mem)   //   > arcsync_top_stub
  , .v0c2_pd_logic                 (v0c2_pd_logic) //   > arcsync_top_stub
  , .v0c2_pd_logic1                (v0c2_pd_logic1) //   > arcsync_top_stub
  , .v0c2_pd_logic2                (v0c2_pd_logic2) //   > arcsync_top_stub
  , .v0c3_isolate_n                (v0c3_isolate_n) //   > arcsync_top_stub
  , .v0c3_isolate                  (v0c3_isolate)  //   > arcsync_top_stub
  , .v0c3_pd_mem                   (v0c3_pd_mem)   //   > arcsync_top_stub
  , .v0c3_pd_logic                 (v0c3_pd_logic) //   > arcsync_top_stub
  , .v0c3_pd_logic1                (v0c3_pd_logic1) //   > arcsync_top_stub
  , .v0c3_pd_logic2                (v0c3_pd_logic2) //   > arcsync_top_stub
  , .arcsync_axi_arready           (arcsync_axi_arready) //   > alb_mss_fab
  , .arcsync_axi_rid               (arcsync_axi_rid) //   > alb_mss_fab
  , .arcsync_axi_rvalid            (arcsync_axi_rvalid) //   > alb_mss_fab
  , .arcsync_axi_rdata             (arcsync_axi_rdata) //   > alb_mss_fab
  , .arcsync_axi_rresp             (arcsync_axi_rresp) //   > alb_mss_fab
  , .arcsync_axi_rlast             (arcsync_axi_rlast) //   > alb_mss_fab
  , .arcsync_axi_awready           (arcsync_axi_awready) //   > alb_mss_fab
  , .arcsync_axi_wready            (arcsync_axi_wready) //   > alb_mss_fab
  , .arcsync_axi_bid               (arcsync_axi_bid) //   > alb_mss_fab
  , .arcsync_axi_bvalid            (arcsync_axi_bvalid) //   > alb_mss_fab
  , .arcsync_axi_bresp             (arcsync_axi_bresp) //   > alb_mss_fab
  , .nl2arc0_ext_arc_run_ack       (nl2arc0_ext_arc_run_ack) //   > outside-of-hierarchy
  , .nl2arc0_ext_arc_halt_ack      (nl2arc0_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .nl2arc1_ext_arc_run_ack       (nl2arc1_ext_arc_run_ack) //   > outside-of-hierarchy
  , .nl2arc1_ext_arc_halt_ack      (nl2arc1_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl0nl1arc_ext_arc_run_ack     (sl0nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl0nl1arc_ext_arc_halt_ack    (sl0nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl1nl1arc_ext_arc_run_ack     (sl1nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl1nl1arc_ext_arc_halt_ack    (sl1nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl2nl1arc_ext_arc_run_ack     (sl2nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl2nl1arc_ext_arc_halt_ack    (sl2nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl3nl1arc_ext_arc_run_ack     (sl3nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl3nl1arc_ext_arc_halt_ack    (sl3nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl4nl1arc_ext_arc_run_ack     (sl4nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl4nl1arc_ext_arc_halt_ack    (sl4nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl5nl1arc_ext_arc_run_ack     (sl5nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl5nl1arc_ext_arc_halt_ack    (sl5nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl6nl1arc_ext_arc_run_ack     (sl6nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl6nl1arc_ext_arc_halt_ack    (sl6nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl7nl1arc_ext_arc_run_ack     (sl7nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl7nl1arc_ext_arc_halt_ack    (sl7nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl8nl1arc_ext_arc_run_ack     (sl8nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl8nl1arc_ext_arc_halt_ack    (sl8nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl9nl1arc_ext_arc_run_ack     (sl9nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl9nl1arc_ext_arc_halt_ack    (sl9nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl10nl1arc_ext_arc_run_ack    (sl10nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl10nl1arc_ext_arc_halt_ack   (sl10nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl11nl1arc_ext_arc_run_ack    (sl11nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl11nl1arc_ext_arc_halt_ack   (sl11nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl12nl1arc_ext_arc_run_ack    (sl12nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl12nl1arc_ext_arc_halt_ack   (sl12nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl13nl1arc_ext_arc_run_ack    (sl13nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl13nl1arc_ext_arc_halt_ack   (sl13nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl14nl1arc_ext_arc_run_ack    (sl14nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl14nl1arc_ext_arc_halt_ack   (sl14nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .sl15nl1arc_ext_arc_run_ack    (sl15nl1arc_ext_arc_run_ack) //   > outside-of-hierarchy
  , .sl15nl1arc_ext_arc_halt_ack   (sl15nl1arc_ext_arc_halt_ack) //   > outside-of-hierarchy
  , .h0host_irq                    (h0host_irq)    //   > outside-of-hierarchy
  , .h0host_event                  (h0host_event)  //   > outside-of-hierarchy
  , .h0host_virt_evt_a             (h0host_virt_evt_a) //   > outside-of-hierarchy
  , .h0host_virt_irq_a             (h0host_virt_irq_a) //   > outside-of-hierarchy
  );

// Output drives
assign nl2arc_isolate_n = i_nl2arc_isolate_n;
assign nl2arc_isolate = i_nl2arc_isolate;
assign nl2arc_pd_mem = i_nl2arc_pd_mem;
assign nl2arc_pd_logic = i_nl2arc_pd_logic;
assign grp0_isolate_n = i_grp0_isolate_n;
assign grp0_isolate = i_grp0_isolate;
assign grp0_pd_mem = i_grp0_pd_mem;
assign grp0_pd_logic = i_grp0_pd_logic;
assign grp1_isolate_n = i_grp1_isolate_n;
assign grp1_isolate = i_grp1_isolate;
assign grp1_pd_mem = i_grp1_pd_mem;
assign grp1_pd_logic = i_grp1_pd_logic;
assign grp2_isolate_n = i_grp2_isolate_n;
assign grp2_isolate = i_grp2_isolate;
assign grp2_pd_mem = i_grp2_pd_mem;
assign grp2_pd_logic = i_grp2_pd_logic;
assign grp3_isolate_n = i_grp3_isolate_n;
assign grp3_isolate = i_grp3_isolate;
assign grp3_pd_mem = i_grp3_pd_mem;
assign grp3_pd_logic = i_grp3_pd_logic;
assign sl0nl1arc_isolate_n = i_sl0nl1arc_isolate_n;
assign sl0nl1arc_isolate = i_sl0nl1arc_isolate;
assign sl0nl1arc_pd_mem = i_sl0nl1arc_pd_mem;
assign sl0nl1arc_pd_logic = i_sl0nl1arc_pd_logic;
assign sl1nl1arc_isolate_n = i_sl1nl1arc_isolate_n;
assign sl1nl1arc_isolate = i_sl1nl1arc_isolate;
assign sl1nl1arc_pd_mem = i_sl1nl1arc_pd_mem;
assign sl1nl1arc_pd_logic = i_sl1nl1arc_pd_logic;
assign sl2nl1arc_isolate_n = i_sl2nl1arc_isolate_n;
assign sl2nl1arc_isolate = i_sl2nl1arc_isolate;
assign sl2nl1arc_pd_mem = i_sl2nl1arc_pd_mem;
assign sl2nl1arc_pd_logic = i_sl2nl1arc_pd_logic;
assign sl3nl1arc_isolate_n = i_sl3nl1arc_isolate_n;
assign sl3nl1arc_isolate = i_sl3nl1arc_isolate;
assign sl3nl1arc_pd_mem = i_sl3nl1arc_pd_mem;
assign sl3nl1arc_pd_logic = i_sl3nl1arc_pd_logic;
assign sl4nl1arc_isolate_n = i_sl4nl1arc_isolate_n;
assign sl4nl1arc_isolate = i_sl4nl1arc_isolate;
assign sl4nl1arc_pd_mem = i_sl4nl1arc_pd_mem;
assign sl4nl1arc_pd_logic = i_sl4nl1arc_pd_logic;
assign sl5nl1arc_isolate_n = i_sl5nl1arc_isolate_n;
assign sl5nl1arc_isolate = i_sl5nl1arc_isolate;
assign sl5nl1arc_pd_mem = i_sl5nl1arc_pd_mem;
assign sl5nl1arc_pd_logic = i_sl5nl1arc_pd_logic;
assign sl6nl1arc_isolate_n = i_sl6nl1arc_isolate_n;
assign sl6nl1arc_isolate = i_sl6nl1arc_isolate;
assign sl6nl1arc_pd_mem = i_sl6nl1arc_pd_mem;
assign sl6nl1arc_pd_logic = i_sl6nl1arc_pd_logic;
assign sl7nl1arc_isolate_n = i_sl7nl1arc_isolate_n;
assign sl7nl1arc_isolate = i_sl7nl1arc_isolate;
assign sl7nl1arc_pd_mem = i_sl7nl1arc_pd_mem;
assign sl7nl1arc_pd_logic = i_sl7nl1arc_pd_logic;
assign sl8nl1arc_isolate_n = i_sl8nl1arc_isolate_n;
assign sl8nl1arc_isolate = i_sl8nl1arc_isolate;
assign sl8nl1arc_pd_mem = i_sl8nl1arc_pd_mem;
assign sl8nl1arc_pd_logic = i_sl8nl1arc_pd_logic;
assign sl9nl1arc_isolate_n = i_sl9nl1arc_isolate_n;
assign sl9nl1arc_isolate = i_sl9nl1arc_isolate;
assign sl9nl1arc_pd_mem = i_sl9nl1arc_pd_mem;
assign sl9nl1arc_pd_logic = i_sl9nl1arc_pd_logic;
assign sl10nl1arc_isolate_n = i_sl10nl1arc_isolate_n;
assign sl10nl1arc_isolate = i_sl10nl1arc_isolate;
assign sl10nl1arc_pd_mem = i_sl10nl1arc_pd_mem;
assign sl10nl1arc_pd_logic = i_sl10nl1arc_pd_logic;
assign sl11nl1arc_isolate_n = i_sl11nl1arc_isolate_n;
assign sl11nl1arc_isolate = i_sl11nl1arc_isolate;
assign sl11nl1arc_pd_mem = i_sl11nl1arc_pd_mem;
assign sl11nl1arc_pd_logic = i_sl11nl1arc_pd_logic;
assign sl12nl1arc_isolate_n = i_sl12nl1arc_isolate_n;
assign sl12nl1arc_isolate = i_sl12nl1arc_isolate;
assign sl12nl1arc_pd_mem = i_sl12nl1arc_pd_mem;
assign sl12nl1arc_pd_logic = i_sl12nl1arc_pd_logic;
assign sl13nl1arc_isolate_n = i_sl13nl1arc_isolate_n;
assign sl13nl1arc_isolate = i_sl13nl1arc_isolate;
assign sl13nl1arc_pd_mem = i_sl13nl1arc_pd_mem;
assign sl13nl1arc_pd_logic = i_sl13nl1arc_pd_logic;
assign sl14nl1arc_isolate_n = i_sl14nl1arc_isolate_n;
assign sl14nl1arc_isolate = i_sl14nl1arc_isolate;
assign sl14nl1arc_pd_mem = i_sl14nl1arc_pd_mem;
assign sl14nl1arc_pd_logic = i_sl14nl1arc_pd_logic;
assign sl15nl1arc_isolate_n = i_sl15nl1arc_isolate_n;
assign sl15nl1arc_isolate = i_sl15nl1arc_isolate;
assign sl15nl1arc_pd_mem = i_sl15nl1arc_pd_mem;
assign sl15nl1arc_pd_logic = i_sl15nl1arc_pd_logic;
endmodule
