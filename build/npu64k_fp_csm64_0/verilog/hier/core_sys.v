// This file was automatically generated.
// Includes found in dependent files:
`include "npu_defines.v"
`include "arcsync_exported_defines.v"
`include "arcsync_defines.v"
`include "alb_mss_fab_defines.v"
`include "alb_mss_mem_defines.v"

module core_sys(
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
  , input  arcsync_axi_clk               //  <   outside-of-hierarchy
  , input  arcsync_axi_rst_a             //  <   outside-of-hierarchy
  , input  arcsync_core_iso_override     //  <   outside-of-hierarchy
  , input  arcsync_clk                   //  <   outside-of-hierarchy
  , input  arcsync_rst_a                 //  <   outside-of-hierarchy
  , input  [0:0] host_axi_arid           //  <   core_sys_stub
  , input  host_axi_arvalid              //  <   core_sys_stub
  , input  [39:0] host_axi_araddr        //  <   core_sys_stub
  , input  [1:0] host_axi_arburst        //  <   core_sys_stub
  , input  [2:0] host_axi_arsize         //  <   core_sys_stub
  , input  host_axi_arlock               //  <   core_sys_stub
  , input  [3:0] host_axi_arlen          //  <   core_sys_stub
  , input  [3:0] host_axi_arcache        //  <   core_sys_stub
  , input  [2:0] host_axi_arprot         //  <   core_sys_stub
  , input  host_axi_rready               //  <   core_sys_stub
  , input  [0:0] host_axi_awid           //  <   core_sys_stub
  , input  host_axi_awvalid              //  <   core_sys_stub
  , input  [39:0] host_axi_awaddr        //  <   core_sys_stub
  , input  [1:0] host_axi_awburst        //  <   core_sys_stub
  , input  [2:0] host_axi_awsize         //  <   core_sys_stub
  , input  host_axi_awlock               //  <   core_sys_stub
  , input  [3:0] host_axi_awlen          //  <   core_sys_stub
  , input  [3:0] host_axi_awcache        //  <   core_sys_stub
  , input  [2:0] host_axi_awprot         //  <   core_sys_stub
  , input  host_axi_wvalid               //  <   core_sys_stub
  , input  [63:0] host_axi_wdata         //  <   core_sys_stub
  , input  [7:0] host_axi_wstrb          //  <   core_sys_stub
  , input  host_axi_wlast                //  <   core_sys_stub
  , input  host_axi_bready               //  <   core_sys_stub
  , input  [3:0] bri4tb_arid             //  <   outside-of-hierarchy
  , input  bri4tb_arvalid                //  <   outside-of-hierarchy
  , input  [39:0] bri4tb_araddr          //  <   outside-of-hierarchy
  , input  [1:0] bri4tb_arburst          //  <   outside-of-hierarchy
  , input  [2:0] bri4tb_arsize           //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_arlen            //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_arcache          //  <   outside-of-hierarchy
  , input  [2:0] bri4tb_arprot           //  <   outside-of-hierarchy
  , input  bri4tb_rready                 //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_awid             //  <   outside-of-hierarchy
  , input  bri4tb_awvalid                //  <   outside-of-hierarchy
  , input  [39:0] bri4tb_awaddr          //  <   outside-of-hierarchy
  , input  [1:0] bri4tb_awburst          //  <   outside-of-hierarchy
  , input  [2:0] bri4tb_awsize           //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_awlen            //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_awcache          //  <   outside-of-hierarchy
  , input  [2:0] bri4tb_awprot           //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_wid              //  <   outside-of-hierarchy
  , input  bri4tb_wvalid                 //  <   outside-of-hierarchy
  , input  [31:0] bri4tb_wdata           //  <   outside-of-hierarchy
  , input  [3:0] bri4tb_wstrb            //  <   outside-of-hierarchy
  , input  bri4tb_wlast                  //  <   outside-of-hierarchy
  , input  bri4tb_bready                 //  <   outside-of-hierarchy
  , input  clk                           //  <   outside-of-hierarchy
  , input  mss_clk                       //  <   outside-of-hierarchy
  , input  mss_fab_mst0_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_mst1_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_mst2_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_mst3_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_mst4_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_mst5_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_mst6_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_slv0_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_slv1_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_slv2_clk_en           //  <   outside-of-hierarchy
  , input  mss_fab_slv3_clk_en           //  <   outside-of-hierarchy
  , input  rst_b                         //  <   outside-of-hierarchy
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
  , output host_axi_arready              //    > core_sys_stub
  , output host_axi_rvalid               //    > core_sys_stub
  , output [0:0] host_axi_rid            //    > core_sys_stub
  , output [63:0] host_axi_rdata         //    > core_sys_stub
  , output [1:0] host_axi_rresp          //    > core_sys_stub
  , output host_axi_rlast                //    > core_sys_stub
  , output host_axi_awready              //    > core_sys_stub
  , output host_axi_wready               //    > core_sys_stub
  , output host_axi_bvalid               //    > core_sys_stub
  , output [0:0] host_axi_bid            //    > core_sys_stub
  , output [1:0] host_axi_bresp          //    > core_sys_stub
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
  , output bri4tb_arready                //    > outside-of-hierarchy
  , output [3:0] bri4tb_rid              //    > outside-of-hierarchy
  , output bri4tb_rvalid                 //    > outside-of-hierarchy
  , output [31:0] bri4tb_rdata           //    > outside-of-hierarchy
  , output [1:0] bri4tb_rresp            //    > outside-of-hierarchy
  , output bri4tb_rlast                  //    > outside-of-hierarchy
  , output bri4tb_awready                //    > outside-of-hierarchy
  , output bri4tb_wready                 //    > outside-of-hierarchy
  , output [3:0] bri4tb_bid              //    > outside-of-hierarchy
  , output bri4tb_bvalid                 //    > outside-of-hierarchy
  , output [1:0] bri4tb_bresp            //    > outside-of-hierarchy
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
wire   i_npu_mst0_axi_arready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_arready
wire   i_npu_mst0_axi_rvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_rvalid
wire   [5-1:0] i_npu_mst0_axi_rid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_rid [5-1:0]
wire   [64-1:0] i_npu_mst0_axi_rdata;    // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_rdata [64-1:0]
wire   [1:0] i_npu_mst0_axi_rresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_rresp [1:0]
wire   i_npu_mst0_axi_rlast;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_rlast
wire   i_npu_mst0_axi_awready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_awready
wire   i_npu_mst0_axi_wready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_wready
wire   i_npu_mst0_axi_bvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_bvalid
wire   [5-1:0] i_npu_mst0_axi_bid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_bid [5-1:0]
wire   [1:0] i_npu_mst0_axi_bresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst0_axi_bresp [1:0]
wire   i_npu_mst1_axi_arready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_arready
wire   i_npu_mst1_axi_rvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_rvalid
wire   [5-1:0] i_npu_mst1_axi_rid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_rid [5-1:0]
wire   [512-1:0] i_npu_mst1_axi_rdata;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_rdata [512-1:0]
wire   [1:0] i_npu_mst1_axi_rresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_rresp [1:0]
wire   i_npu_mst1_axi_rlast;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_rlast
wire   i_npu_mst1_axi_awready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_awready
wire   i_npu_mst1_axi_wready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_wready
wire   i_npu_mst1_axi_bvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_bvalid
wire   [5-1:0] i_npu_mst1_axi_bid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_bid [5-1:0]
wire   [1:0] i_npu_mst1_axi_bresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst1_axi_bresp [1:0]
wire   i_npu_mst2_axi_arready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_arready
wire   i_npu_mst2_axi_rvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_rvalid
wire   [5-1:0] i_npu_mst2_axi_rid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_rid [5-1:0]
wire   [512-1:0] i_npu_mst2_axi_rdata;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_rdata [512-1:0]
wire   [1:0] i_npu_mst2_axi_rresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_rresp [1:0]
wire   i_npu_mst2_axi_rlast;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_rlast
wire   i_npu_mst2_axi_awready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_awready
wire   i_npu_mst2_axi_wready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_wready
wire   i_npu_mst2_axi_bvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_bvalid
wire   [5-1:0] i_npu_mst2_axi_bid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_bid [5-1:0]
wire   [1:0] i_npu_mst2_axi_bresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst2_axi_bresp [1:0]
wire   i_npu_mst3_axi_arready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_arready
wire   i_npu_mst3_axi_rvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_rvalid
wire   [5-1:0] i_npu_mst3_axi_rid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_rid [5-1:0]
wire   [512-1:0] i_npu_mst3_axi_rdata;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_rdata [512-1:0]
wire   [1:0] i_npu_mst3_axi_rresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_rresp [1:0]
wire   i_npu_mst3_axi_rlast;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_rlast
wire   i_npu_mst3_axi_awready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_awready
wire   i_npu_mst3_axi_wready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_wready
wire   i_npu_mst3_axi_bvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_bvalid
wire   [5-1:0] i_npu_mst3_axi_bid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_bid [5-1:0]
wire   [1:0] i_npu_mst3_axi_bresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst3_axi_bresp [1:0]
wire   i_npu_mst4_axi_arready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_arready
wire   i_npu_mst4_axi_rvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_rvalid
wire   [5-1:0] i_npu_mst4_axi_rid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_rid [5-1:0]
wire   [512-1:0] i_npu_mst4_axi_rdata;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_rdata [512-1:0]
wire   [1:0] i_npu_mst4_axi_rresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_rresp [1:0]
wire   i_npu_mst4_axi_rlast;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_rlast
wire   i_npu_mst4_axi_awready;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_awready
wire   i_npu_mst4_axi_wready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_wready
wire   i_npu_mst4_axi_bvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_bvalid
wire   [5-1:0] i_npu_mst4_axi_bid;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_bid [5-1:0]
wire   [1:0] i_npu_mst4_axi_bresp;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_mst4_axi_bresp [1:0]
wire   i_npu_dmi0_axi_arvalid;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arvalid
wire   [16-1:0] i_npu_dmi0_axi_arid;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arid [16-1:0]
wire   [40-1:0] i_npu_dmi0_axi_araddr;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_araddr [40-1:0]
wire   [3:0] i_npu_dmi0_axi_arcache;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arcache [3:0]
wire   [2:0] i_npu_dmi0_axi_arprot;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arprot [2:0]
wire   i_npu_dmi0_axi_arlock;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arlock
wire   [1:0] i_npu_dmi0_axi_arburst;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arburst [1:0]
wire   [3:0] i_npu_dmi0_axi_arlen;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arlen [3:0]
wire   [2:0] i_npu_dmi0_axi_arsize;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_arsize [2:0]
wire   i_npu_dmi0_axi_rready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_rready
wire   i_npu_dmi0_axi_awvalid;           // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awvalid
wire   [16-1:0] i_npu_dmi0_axi_awid;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awid [16-1:0]
wire   [40-1:0] i_npu_dmi0_axi_awaddr;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awaddr [40-1:0]
wire   [3:0] i_npu_dmi0_axi_awcache;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awcache [3:0]
wire   [2:0] i_npu_dmi0_axi_awprot;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awprot [2:0]
wire   i_npu_dmi0_axi_awlock;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awlock
wire   [1:0] i_npu_dmi0_axi_awburst;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awburst [1:0]
wire   [3:0] i_npu_dmi0_axi_awlen;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awlen [3:0]
wire   [2:0] i_npu_dmi0_axi_awsize;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_awsize [2:0]
wire   i_npu_dmi0_axi_wvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_wvalid
wire   [512-1:0] i_npu_dmi0_axi_wdata;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_wdata [512-1:0]
wire   [512/8-1:0] i_npu_dmi0_axi_wstrb; // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_wstrb [512/8-1:0]
wire   i_npu_dmi0_axi_wlast;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_wlast
wire   i_npu_dmi0_axi_bready;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_dmi0_axi_bready
wire   i_npu_cfg_axi_arvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arvalid
wire   [16-1:0] i_npu_cfg_axi_arid;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arid [16-1:0]
wire   [40-1:0] i_npu_cfg_axi_araddr;    // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_araddr [40-1:0]
wire   [3:0] i_npu_cfg_axi_arcache;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arcache [3:0]
wire   [2:0] i_npu_cfg_axi_arprot;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arprot [2:0]
wire   i_npu_cfg_axi_arlock;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arlock
wire   [1:0] i_npu_cfg_axi_arburst;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arburst [1:0]
wire   [3:0] i_npu_cfg_axi_arlen;        // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arlen [3:0]
wire   [2:0] i_npu_cfg_axi_arsize;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_arsize [2:0]
wire   i_npu_cfg_axi_rready;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_rready
wire   i_npu_cfg_axi_awvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awvalid
wire   [16-1:0] i_npu_cfg_axi_awid;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awid [16-1:0]
wire   [40-1:0] i_npu_cfg_axi_awaddr;    // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awaddr [40-1:0]
wire   [3:0] i_npu_cfg_axi_awcache;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awcache [3:0]
wire   [2:0] i_npu_cfg_axi_awprot;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awprot [2:0]
wire   i_npu_cfg_axi_awlock;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awlock
wire   [1:0] i_npu_cfg_axi_awburst;      // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awburst [1:0]
wire   [3:0] i_npu_cfg_axi_awlen;        // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awlen [3:0]
wire   [2:0] i_npu_cfg_axi_awsize;       // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_awsize [2:0]
wire   i_npu_cfg_axi_wvalid;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_wvalid
wire   [32-1:0] i_npu_cfg_axi_wdata;     // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_wdata [32-1:0]
wire   [32/8-1:0] i_npu_cfg_axi_wstrb;   // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_wstrb [32/8-1:0]
wire   i_npu_cfg_axi_wlast;              // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_wlast
wire   i_npu_cfg_axi_bready;             // alb_mss_fab > core_archipelago -- alb_mss_fab.npu_cfg_axi_bready
wire   i_arcsync_axi_arvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arvalid
wire   [16-1:0] i_arcsync_axi_arid;      // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arid [16-1:0]
wire   [40-1:0] i_arcsync_axi_araddr;    // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_araddr [40-1:0]
wire   [3:0] i_arcsync_axi_arcache;      // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arcache [3:0]
wire   [2:0] i_arcsync_axi_arprot;       // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arprot [2:0]
wire   i_arcsync_axi_arlock;             // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arlock
wire   [1:0] i_arcsync_axi_arburst;      // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arburst [1:0]
wire   [3:0] i_arcsync_axi_arlen;        // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arlen [3:0]
wire   [2:0] i_arcsync_axi_arsize;       // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_arsize [2:0]
wire   i_arcsync_axi_rready;             // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_rready
wire   i_arcsync_axi_awvalid;            // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awvalid
wire   [16-1:0] i_arcsync_axi_awid;      // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awid [16-1:0]
wire   [40-1:0] i_arcsync_axi_awaddr;    // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awaddr [40-1:0]
wire   [3:0] i_arcsync_axi_awcache;      // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awcache [3:0]
wire   [2:0] i_arcsync_axi_awprot;       // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awprot [2:0]
wire   i_arcsync_axi_awlock;             // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awlock
wire   [1:0] i_arcsync_axi_awburst;      // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awburst [1:0]
wire   [3:0] i_arcsync_axi_awlen;        // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awlen [3:0]
wire   [2:0] i_arcsync_axi_awsize;       // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_awsize [2:0]
wire   i_arcsync_axi_wvalid;             // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_wvalid
wire   [64-1:0] i_arcsync_axi_wdata;     // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_wdata [64-1:0]
wire   [64/8-1:0] i_arcsync_axi_wstrb;   // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_wstrb [64/8-1:0]
wire   i_arcsync_axi_wlast;              // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_wlast
wire   i_arcsync_axi_bready;             // alb_mss_fab > core_archipelago -- alb_mss_fab.arcsync_axi_bready
wire   i_v0c0arc_halt_ack_a;             // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0arc_halt_ack_a
wire   i_v0c0ext_arc_halt_req_a;         // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0ext_arc_halt_req_a
wire   i_v0c0arc_run_ack_a;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0arc_run_ack_a
wire   i_v0c0ext_arc_run_req_a;          // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0ext_arc_run_req_a
wire   i_v0c0sys_sleep_r;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0sys_sleep_r
wire   [2:0] i_v0c0sys_sleep_mode_r;     // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0sys_sleep_mode_r [2:0]
wire   i_v0c0sys_halt_r;                 // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0sys_halt_r
wire   i_v0c0sys_tf_halt_r;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0sys_tf_halt_r
wire   [2:0] i_v0c0pmode;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c0pmode [2:0]
wire   i_v0c1arc_halt_ack_a;             // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1arc_halt_ack_a
wire   i_v0c1ext_arc_halt_req_a;         // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1ext_arc_halt_req_a
wire   i_v0c1arc_run_ack_a;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1arc_run_ack_a
wire   i_v0c1ext_arc_run_req_a;          // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1ext_arc_run_req_a
wire   i_v0c1sys_sleep_r;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1sys_sleep_r
wire   [2:0] i_v0c1sys_sleep_mode_r;     // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1sys_sleep_mode_r [2:0]
wire   i_v0c1sys_halt_r;                 // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1sys_halt_r
wire   i_v0c1sys_tf_halt_r;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1sys_tf_halt_r
wire   [2:0] i_v0c1pmode;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c1pmode [2:0]
wire   i_v0c2arc_halt_ack_a;             // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2arc_halt_ack_a
wire   i_v0c2ext_arc_halt_req_a;         // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2ext_arc_halt_req_a
wire   i_v0c2arc_run_ack_a;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2arc_run_ack_a
wire   i_v0c2ext_arc_run_req_a;          // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2ext_arc_run_req_a
wire   i_v0c2sys_sleep_r;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2sys_sleep_r
wire   [2:0] i_v0c2sys_sleep_mode_r;     // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2sys_sleep_mode_r [2:0]
wire   i_v0c2sys_halt_r;                 // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2sys_halt_r
wire   i_v0c2sys_tf_halt_r;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2sys_tf_halt_r
wire   [2:0] i_v0c2pmode;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c2pmode [2:0]
wire   i_v0c3arc_halt_ack_a;             // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3arc_halt_ack_a
wire   i_v0c3ext_arc_halt_req_a;         // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3ext_arc_halt_req_a
wire   i_v0c3arc_run_ack_a;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3arc_run_ack_a
wire   i_v0c3ext_arc_run_req_a;          // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3ext_arc_run_req_a
wire   i_v0c3sys_sleep_r;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3sys_sleep_r
wire   [2:0] i_v0c3sys_sleep_mode_r;     // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3sys_sleep_mode_r [2:0]
wire   i_v0c3sys_halt_r;                 // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3sys_halt_r
wire   i_v0c3sys_tf_halt_r;              // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3sys_tf_halt_r
wire   [2:0] i_v0c3pmode;                // arcsync_top_stub > core_archipelago -- arcsync_top_stub.v0c3pmode [2:0]
wire   i_nl2arc_isolate_n;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.nl2arc_isolate_n
wire   i_nl2arc_isolate;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.nl2arc_isolate
wire   i_nl2arc_pd_mem;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.nl2arc_pd_mem
wire   i_nl2arc_pd_logic;                // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.nl2arc_pd_logic
wire   i_nl2arc_pd_logic1;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.nl2arc_pd_logic1
wire   i_nl2arc_pd_logic2;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.nl2arc_pd_logic2
wire   i_grp0_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp0_isolate_n
wire   i_grp0_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp0_isolate
wire   i_grp0_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp0_pd_mem
wire   i_grp0_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp0_pd_logic
wire   i_grp0_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp0_pd_logic1
wire   i_grp0_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp0_pd_logic2
wire   i_grp1_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp1_isolate_n
wire   i_grp1_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp1_isolate
wire   i_grp1_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp1_pd_mem
wire   i_grp1_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp1_pd_logic
wire   i_grp1_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp1_pd_logic1
wire   i_grp1_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp1_pd_logic2
wire   i_grp2_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp2_isolate_n
wire   i_grp2_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp2_isolate
wire   i_grp2_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp2_pd_mem
wire   i_grp2_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp2_pd_logic
wire   i_grp2_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp2_pd_logic1
wire   i_grp2_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp2_pd_logic2
wire   i_grp3_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp3_isolate_n
wire   i_grp3_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp3_isolate
wire   i_grp3_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp3_pd_mem
wire   i_grp3_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp3_pd_logic
wire   i_grp3_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp3_pd_logic1
wire   i_grp3_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.grp3_pd_logic2
wire   i_sl0nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl0nl1arc_isolate_n
wire   i_sl0nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl0nl1arc_isolate
wire   i_sl0nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl0nl1arc_pd_mem
wire   i_sl0nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl0nl1arc_pd_logic
wire   i_sl0nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl0nl1arc_pd_logic1
wire   i_sl0nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl0nl1arc_pd_logic2
wire   i_sl1nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl1nl1arc_isolate_n
wire   i_sl1nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl1nl1arc_isolate
wire   i_sl1nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl1nl1arc_pd_mem
wire   i_sl1nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl1nl1arc_pd_logic
wire   i_sl1nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl1nl1arc_pd_logic1
wire   i_sl1nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl1nl1arc_pd_logic2
wire   i_sl2nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl2nl1arc_isolate_n
wire   i_sl2nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl2nl1arc_isolate
wire   i_sl2nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl2nl1arc_pd_mem
wire   i_sl2nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl2nl1arc_pd_logic
wire   i_sl2nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl2nl1arc_pd_logic1
wire   i_sl2nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl2nl1arc_pd_logic2
wire   i_sl3nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl3nl1arc_isolate_n
wire   i_sl3nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl3nl1arc_isolate
wire   i_sl3nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl3nl1arc_pd_mem
wire   i_sl3nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl3nl1arc_pd_logic
wire   i_sl3nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl3nl1arc_pd_logic1
wire   i_sl3nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl3nl1arc_pd_logic2
wire   i_sl4nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl4nl1arc_isolate_n
wire   i_sl4nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl4nl1arc_isolate
wire   i_sl4nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl4nl1arc_pd_mem
wire   i_sl4nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl4nl1arc_pd_logic
wire   i_sl4nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl4nl1arc_pd_logic1
wire   i_sl4nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl4nl1arc_pd_logic2
wire   i_sl5nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl5nl1arc_isolate_n
wire   i_sl5nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl5nl1arc_isolate
wire   i_sl5nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl5nl1arc_pd_mem
wire   i_sl5nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl5nl1arc_pd_logic
wire   i_sl5nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl5nl1arc_pd_logic1
wire   i_sl5nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl5nl1arc_pd_logic2
wire   i_sl6nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl6nl1arc_isolate_n
wire   i_sl6nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl6nl1arc_isolate
wire   i_sl6nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl6nl1arc_pd_mem
wire   i_sl6nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl6nl1arc_pd_logic
wire   i_sl6nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl6nl1arc_pd_logic1
wire   i_sl6nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl6nl1arc_pd_logic2
wire   i_sl7nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl7nl1arc_isolate_n
wire   i_sl7nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl7nl1arc_isolate
wire   i_sl7nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl7nl1arc_pd_mem
wire   i_sl7nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl7nl1arc_pd_logic
wire   i_sl7nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl7nl1arc_pd_logic1
wire   i_sl7nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl7nl1arc_pd_logic2
wire   i_sl8nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl8nl1arc_isolate_n
wire   i_sl8nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl8nl1arc_isolate
wire   i_sl8nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl8nl1arc_pd_mem
wire   i_sl8nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl8nl1arc_pd_logic
wire   i_sl8nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl8nl1arc_pd_logic1
wire   i_sl8nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl8nl1arc_pd_logic2
wire   i_sl9nl1arc_isolate_n;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl9nl1arc_isolate_n
wire   i_sl9nl1arc_isolate;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl9nl1arc_isolate
wire   i_sl9nl1arc_pd_mem;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl9nl1arc_pd_mem
wire   i_sl9nl1arc_pd_logic;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl9nl1arc_pd_logic
wire   i_sl9nl1arc_pd_logic1;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl9nl1arc_pd_logic1
wire   i_sl9nl1arc_pd_logic2;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl9nl1arc_pd_logic2
wire   i_sl10nl1arc_isolate_n;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl10nl1arc_isolate_n
wire   i_sl10nl1arc_isolate;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl10nl1arc_isolate
wire   i_sl10nl1arc_pd_mem;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl10nl1arc_pd_mem
wire   i_sl10nl1arc_pd_logic;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl10nl1arc_pd_logic
wire   i_sl10nl1arc_pd_logic1;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl10nl1arc_pd_logic1
wire   i_sl10nl1arc_pd_logic2;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl10nl1arc_pd_logic2
wire   i_sl11nl1arc_isolate_n;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl11nl1arc_isolate_n
wire   i_sl11nl1arc_isolate;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl11nl1arc_isolate
wire   i_sl11nl1arc_pd_mem;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl11nl1arc_pd_mem
wire   i_sl11nl1arc_pd_logic;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl11nl1arc_pd_logic
wire   i_sl11nl1arc_pd_logic1;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl11nl1arc_pd_logic1
wire   i_sl11nl1arc_pd_logic2;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl11nl1arc_pd_logic2
wire   i_sl12nl1arc_isolate_n;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl12nl1arc_isolate_n
wire   i_sl12nl1arc_isolate;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl12nl1arc_isolate
wire   i_sl12nl1arc_pd_mem;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl12nl1arc_pd_mem
wire   i_sl12nl1arc_pd_logic;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl12nl1arc_pd_logic
wire   i_sl12nl1arc_pd_logic1;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl12nl1arc_pd_logic1
wire   i_sl12nl1arc_pd_logic2;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl12nl1arc_pd_logic2
wire   i_sl13nl1arc_isolate_n;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl13nl1arc_isolate_n
wire   i_sl13nl1arc_isolate;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl13nl1arc_isolate
wire   i_sl13nl1arc_pd_mem;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl13nl1arc_pd_mem
wire   i_sl13nl1arc_pd_logic;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl13nl1arc_pd_logic
wire   i_sl13nl1arc_pd_logic1;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl13nl1arc_pd_logic1
wire   i_sl13nl1arc_pd_logic2;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl13nl1arc_pd_logic2
wire   i_sl14nl1arc_isolate_n;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl14nl1arc_isolate_n
wire   i_sl14nl1arc_isolate;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl14nl1arc_isolate
wire   i_sl14nl1arc_pd_mem;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl14nl1arc_pd_mem
wire   i_sl14nl1arc_pd_logic;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl14nl1arc_pd_logic
wire   i_sl14nl1arc_pd_logic1;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl14nl1arc_pd_logic1
wire   i_sl14nl1arc_pd_logic2;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl14nl1arc_pd_logic2
wire   i_sl15nl1arc_isolate_n;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl15nl1arc_isolate_n
wire   i_sl15nl1arc_isolate;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl15nl1arc_isolate
wire   i_sl15nl1arc_pd_mem;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl15nl1arc_pd_mem
wire   i_sl15nl1arc_pd_logic;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl15nl1arc_pd_logic
wire   i_sl15nl1arc_pd_logic1;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl15nl1arc_pd_logic1
wire   i_sl15nl1arc_pd_logic2;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.sl15nl1arc_pd_logic2
wire   [39:16] i_v0csm_addr_base;        // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0csm_addr_base [39:16]
wire   [39:16] i_v0periph_addr_base;     // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0periph_addr_base [39:16]
wire   [7:0] i_v0clusternum;             // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0clusternum [7:0]
wire   [7:0] i_v0c0arcnum;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arcnum [7:0]
wire   [31:10] i_v0c0intvbase;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0intvbase [31:10]
wire   i_v0c0rst_a;                      // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0rst_a
wire   i_v0c0clk_en;                     // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0clk_en
wire   i_v0c0arc_halt_req;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arc_halt_req
wire   i_v0c0ext_arc_halt_ack;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0ext_arc_halt_ack
wire   i_v0c0arc_run_req;                // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arc_run_req
wire   i_v0c0ext_arc_run_ack;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0ext_arc_run_ack
wire   i_v0c0arc_irq0_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arc_irq0_a
wire   i_v0c0arc_irq1_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arc_irq1_a
wire   i_v0c0arc_event0_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arc_event0_a
wire   i_v0c0arc_event1_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0arc_event1_a
wire   [7:0] i_v0c1arcnum;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arcnum [7:0]
wire   [31:10] i_v0c1intvbase;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1intvbase [31:10]
wire   i_v0c1rst_a;                      // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1rst_a
wire   i_v0c1clk_en;                     // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1clk_en
wire   i_v0c1arc_halt_req;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arc_halt_req
wire   i_v0c1ext_arc_halt_ack;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1ext_arc_halt_ack
wire   i_v0c1arc_run_req;                // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arc_run_req
wire   i_v0c1ext_arc_run_ack;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1ext_arc_run_ack
wire   i_v0c1arc_irq0_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arc_irq0_a
wire   i_v0c1arc_irq1_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arc_irq1_a
wire   i_v0c1arc_event0_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arc_event0_a
wire   i_v0c1arc_event1_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1arc_event1_a
wire   [7:0] i_v0c2arcnum;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arcnum [7:0]
wire   [31:10] i_v0c2intvbase;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2intvbase [31:10]
wire   i_v0c2rst_a;                      // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2rst_a
wire   i_v0c2clk_en;                     // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2clk_en
wire   i_v0c2arc_halt_req;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arc_halt_req
wire   i_v0c2ext_arc_halt_ack;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2ext_arc_halt_ack
wire   i_v0c2arc_run_req;                // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arc_run_req
wire   i_v0c2ext_arc_run_ack;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2ext_arc_run_ack
wire   i_v0c2arc_irq0_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arc_irq0_a
wire   i_v0c2arc_irq1_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arc_irq1_a
wire   i_v0c2arc_event0_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arc_event0_a
wire   i_v0c2arc_event1_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2arc_event1_a
wire   [7:0] i_v0c3arcnum;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arcnum [7:0]
wire   [31:10] i_v0c3intvbase;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3intvbase [31:10]
wire   i_v0c3rst_a;                      // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3rst_a
wire   i_v0c3clk_en;                     // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3clk_en
wire   i_v0c3arc_halt_req;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arc_halt_req
wire   i_v0c3ext_arc_halt_ack;           // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3ext_arc_halt_ack
wire   i_v0c3arc_run_req;                // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arc_run_req
wire   i_v0c3ext_arc_run_ack;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3ext_arc_run_ack
wire   i_v0c3arc_irq0_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arc_irq0_a
wire   i_v0c3arc_irq1_a;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arc_irq1_a
wire   i_v0c3arc_event0_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arc_event0_a
wire   i_v0c3arc_event1_a;               // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3arc_event1_a
wire   i_vpx_v0_vm0_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm0_irq0_a
wire   i_vpx_v0_vm0_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm0_irq_ac_a
wire   i_vpx_v0_vm0_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm0_evt0_a
wire   i_vpx_v0_vm0_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm0_evt_ac_a
wire   i_vpx_v0_vm1_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm1_irq0_a
wire   i_vpx_v0_vm1_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm1_irq_ac_a
wire   i_vpx_v0_vm1_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm1_evt0_a
wire   i_vpx_v0_vm1_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm1_evt_ac_a
wire   i_vpx_v0_vm2_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm2_irq0_a
wire   i_vpx_v0_vm2_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm2_irq_ac_a
wire   i_vpx_v0_vm2_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm2_evt0_a
wire   i_vpx_v0_vm2_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm2_evt_ac_a
wire   i_vpx_v0_vm3_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm3_irq0_a
wire   i_vpx_v0_vm3_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm3_irq_ac_a
wire   i_vpx_v0_vm3_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm3_evt0_a
wire   i_vpx_v0_vm3_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm3_evt_ac_a
wire   i_vpx_v0_vm4_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm4_irq0_a
wire   i_vpx_v0_vm4_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm4_irq_ac_a
wire   i_vpx_v0_vm4_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm4_evt0_a
wire   i_vpx_v0_vm4_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm4_evt_ac_a
wire   i_vpx_v0_vm5_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm5_irq0_a
wire   i_vpx_v0_vm5_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm5_irq_ac_a
wire   i_vpx_v0_vm5_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm5_evt0_a
wire   i_vpx_v0_vm5_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm5_evt_ac_a
wire   i_vpx_v0_vm6_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm6_irq0_a
wire   i_vpx_v0_vm6_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm6_irq_ac_a
wire   i_vpx_v0_vm6_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm6_evt0_a
wire   i_vpx_v0_vm6_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm6_evt_ac_a
wire   i_vpx_v0_vm7_irq0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm7_irq0_a
wire   i_vpx_v0_vm7_irq_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm7_irq_ac_a
wire   i_vpx_v0_vm7_evt0_a;              // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm7_evt0_a
wire   i_vpx_v0_vm7_evt_ac_a;            // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.vpx_v0_vm7_evt_ac_a
wire   i_v0c0_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0_isolate_n
wire   i_v0c0_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0_isolate
wire   i_v0c0_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0_pd_mem
wire   i_v0c0_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0_pd_logic
wire   i_v0c0_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0_pd_logic1
wire   i_v0c0_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c0_pd_logic2
wire   i_v0c1_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1_isolate_n
wire   i_v0c1_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1_isolate
wire   i_v0c1_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1_pd_mem
wire   i_v0c1_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1_pd_logic
wire   i_v0c1_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1_pd_logic1
wire   i_v0c1_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c1_pd_logic2
wire   i_v0c2_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2_isolate_n
wire   i_v0c2_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2_isolate
wire   i_v0c2_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2_pd_mem
wire   i_v0c2_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2_pd_logic
wire   i_v0c2_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2_pd_logic1
wire   i_v0c2_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c2_pd_logic2
wire   i_v0c3_isolate_n;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3_isolate_n
wire   i_v0c3_isolate;                   // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3_isolate
wire   i_v0c3_pd_mem;                    // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3_pd_mem
wire   i_v0c3_pd_logic;                  // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3_pd_logic
wire   i_v0c3_pd_logic1;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3_pd_logic1
wire   i_v0c3_pd_logic2;                 // core_archipelago > arcsync_top_stub -- core_archipelago.arcsync_top.v0c3_pd_logic2
wire   [4:0] i_npu_mst0_axi_arid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arid [4:0]
wire   i_npu_mst0_axi_arvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arvalid
wire   [39:0] i_npu_mst0_axi_araddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_araddr [39:0]
wire   [1:0] i_npu_mst0_axi_arburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arburst [1:0]
wire   [2:0] i_npu_mst0_axi_arsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arsize [2:0]
wire   [0:0] i_npu_mst0_axi_arlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arlock [0:0]
wire   [3:0] i_npu_mst0_axi_arlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arlen [3:0]
wire   [3:0] i_npu_mst0_axi_arcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arcache [3:0]
wire   [2:0] i_npu_mst0_axi_arprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_arprot [2:0]
wire   i_npu_mst0_axi_rready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_rready
wire   [4:0] i_npu_mst0_axi_awid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awid [4:0]
wire   i_npu_mst0_axi_awvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awvalid
wire   [39:0] i_npu_mst0_axi_awaddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awaddr [39:0]
wire   [1:0] i_npu_mst0_axi_awburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awburst [1:0]
wire   [2:0] i_npu_mst0_axi_awsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awsize [2:0]
wire   [0:0] i_npu_mst0_axi_awlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awlock [0:0]
wire   [3:0] i_npu_mst0_axi_awlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awlen [3:0]
wire   [3:0] i_npu_mst0_axi_awcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awcache [3:0]
wire   [2:0] i_npu_mst0_axi_awprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_awprot [2:0]
wire   i_npu_mst0_axi_wvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_wvalid
wire   [63:0] i_npu_mst0_axi_wdata;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_wdata [63:0]
wire   [7:0] i_npu_mst0_axi_wstrb;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_wstrb [7:0]
wire   i_npu_mst0_axi_wlast;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_wlast
wire   i_npu_mst0_axi_bready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst0_axi_bready
wire   [4:0] i_npu_mst1_axi_arid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arid [4:0]
wire   i_npu_mst1_axi_arvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arvalid
wire   [39:0] i_npu_mst1_axi_araddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_araddr [39:0]
wire   [1:0] i_npu_mst1_axi_arburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arburst [1:0]
wire   [2:0] i_npu_mst1_axi_arsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arsize [2:0]
wire   [0:0] i_npu_mst1_axi_arlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arlock [0:0]
wire   [3:0] i_npu_mst1_axi_arlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arlen [3:0]
wire   [3:0] i_npu_mst1_axi_arcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arcache [3:0]
wire   [2:0] i_npu_mst1_axi_arprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_arprot [2:0]
wire   i_npu_mst1_axi_rready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_rready
wire   [4:0] i_npu_mst1_axi_awid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awid [4:0]
wire   i_npu_mst1_axi_awvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awvalid
wire   [39:0] i_npu_mst1_axi_awaddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awaddr [39:0]
wire   [1:0] i_npu_mst1_axi_awburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awburst [1:0]
wire   [2:0] i_npu_mst1_axi_awsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awsize [2:0]
wire   [0:0] i_npu_mst1_axi_awlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awlock [0:0]
wire   [3:0] i_npu_mst1_axi_awlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awlen [3:0]
wire   [3:0] i_npu_mst1_axi_awcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awcache [3:0]
wire   [2:0] i_npu_mst1_axi_awprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_awprot [2:0]
wire   i_npu_mst1_axi_wvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_wvalid
wire   [511:0] i_npu_mst1_axi_wdata;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_wdata [511:0]
wire   [63:0] i_npu_mst1_axi_wstrb;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_wstrb [63:0]
wire   i_npu_mst1_axi_wlast;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_wlast
wire   i_npu_mst1_axi_bready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst1_axi_bready
wire   [4:0] i_npu_mst2_axi_arid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arid [4:0]
wire   i_npu_mst2_axi_arvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arvalid
wire   [39:0] i_npu_mst2_axi_araddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_araddr [39:0]
wire   [1:0] i_npu_mst2_axi_arburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arburst [1:0]
wire   [2:0] i_npu_mst2_axi_arsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arsize [2:0]
wire   [0:0] i_npu_mst2_axi_arlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arlock [0:0]
wire   [3:0] i_npu_mst2_axi_arlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arlen [3:0]
wire   [3:0] i_npu_mst2_axi_arcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arcache [3:0]
wire   [2:0] i_npu_mst2_axi_arprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_arprot [2:0]
wire   i_npu_mst2_axi_rready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_rready
wire   [4:0] i_npu_mst2_axi_awid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awid [4:0]
wire   i_npu_mst2_axi_awvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awvalid
wire   [39:0] i_npu_mst2_axi_awaddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awaddr [39:0]
wire   [1:0] i_npu_mst2_axi_awburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awburst [1:0]
wire   [2:0] i_npu_mst2_axi_awsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awsize [2:0]
wire   [0:0] i_npu_mst2_axi_awlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awlock [0:0]
wire   [3:0] i_npu_mst2_axi_awlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awlen [3:0]
wire   [3:0] i_npu_mst2_axi_awcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awcache [3:0]
wire   [2:0] i_npu_mst2_axi_awprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_awprot [2:0]
wire   i_npu_mst2_axi_wvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_wvalid
wire   [511:0] i_npu_mst2_axi_wdata;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_wdata [511:0]
wire   [63:0] i_npu_mst2_axi_wstrb;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_wstrb [63:0]
wire   i_npu_mst2_axi_wlast;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_wlast
wire   i_npu_mst2_axi_bready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst2_axi_bready
wire   [4:0] i_npu_mst3_axi_arid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arid [4:0]
wire   i_npu_mst3_axi_arvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arvalid
wire   [39:0] i_npu_mst3_axi_araddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_araddr [39:0]
wire   [1:0] i_npu_mst3_axi_arburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arburst [1:0]
wire   [2:0] i_npu_mst3_axi_arsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arsize [2:0]
wire   [0:0] i_npu_mst3_axi_arlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arlock [0:0]
wire   [3:0] i_npu_mst3_axi_arlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arlen [3:0]
wire   [3:0] i_npu_mst3_axi_arcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arcache [3:0]
wire   [2:0] i_npu_mst3_axi_arprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_arprot [2:0]
wire   i_npu_mst3_axi_rready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_rready
wire   [4:0] i_npu_mst3_axi_awid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awid [4:0]
wire   i_npu_mst3_axi_awvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awvalid
wire   [39:0] i_npu_mst3_axi_awaddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awaddr [39:0]
wire   [1:0] i_npu_mst3_axi_awburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awburst [1:0]
wire   [2:0] i_npu_mst3_axi_awsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awsize [2:0]
wire   [0:0] i_npu_mst3_axi_awlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awlock [0:0]
wire   [3:0] i_npu_mst3_axi_awlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awlen [3:0]
wire   [3:0] i_npu_mst3_axi_awcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awcache [3:0]
wire   [2:0] i_npu_mst3_axi_awprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_awprot [2:0]
wire   i_npu_mst3_axi_wvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_wvalid
wire   [511:0] i_npu_mst3_axi_wdata;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_wdata [511:0]
wire   [63:0] i_npu_mst3_axi_wstrb;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_wstrb [63:0]
wire   i_npu_mst3_axi_wlast;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_wlast
wire   i_npu_mst3_axi_bready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst3_axi_bready
wire   [4:0] i_npu_mst4_axi_arid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arid [4:0]
wire   i_npu_mst4_axi_arvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arvalid
wire   [39:0] i_npu_mst4_axi_araddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_araddr [39:0]
wire   [1:0] i_npu_mst4_axi_arburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arburst [1:0]
wire   [2:0] i_npu_mst4_axi_arsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arsize [2:0]
wire   [0:0] i_npu_mst4_axi_arlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arlock [0:0]
wire   [3:0] i_npu_mst4_axi_arlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arlen [3:0]
wire   [3:0] i_npu_mst4_axi_arcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arcache [3:0]
wire   [2:0] i_npu_mst4_axi_arprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_arprot [2:0]
wire   i_npu_mst4_axi_rready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_rready
wire   [4:0] i_npu_mst4_axi_awid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awid [4:0]
wire   i_npu_mst4_axi_awvalid;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awvalid
wire   [39:0] i_npu_mst4_axi_awaddr;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awaddr [39:0]
wire   [1:0] i_npu_mst4_axi_awburst;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awburst [1:0]
wire   [2:0] i_npu_mst4_axi_awsize;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awsize [2:0]
wire   [0:0] i_npu_mst4_axi_awlock;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awlock [0:0]
wire   [3:0] i_npu_mst4_axi_awlen;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awlen [3:0]
wire   [3:0] i_npu_mst4_axi_awcache;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awcache [3:0]
wire   [2:0] i_npu_mst4_axi_awprot;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_awprot [2:0]
wire   i_npu_mst4_axi_wvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_wvalid
wire   [511:0] i_npu_mst4_axi_wdata;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_wdata [511:0]
wire   [63:0] i_npu_mst4_axi_wstrb;      // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_wstrb [63:0]
wire   i_npu_mst4_axi_wlast;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_wlast
wire   i_npu_mst4_axi_bready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_mst4_axi_bready
wire   i_npu_dmi0_axi_arready;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_arready
wire   [15:0] i_npu_dmi0_axi_rid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_rid [15:0]
wire   i_npu_dmi0_axi_rvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_rvalid
wire   [511:0] i_npu_dmi0_axi_rdata;     // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_rdata [511:0]
wire   [1:0] i_npu_dmi0_axi_rresp;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_rresp [1:0]
wire   i_npu_dmi0_axi_rlast;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_rlast
wire   i_npu_dmi0_axi_awready;           // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_awready
wire   i_npu_dmi0_axi_wready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_wready
wire   [15:0] i_npu_dmi0_axi_bid;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_bid [15:0]
wire   i_npu_dmi0_axi_bvalid;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_bvalid
wire   [1:0] i_npu_dmi0_axi_bresp;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_dmi0_axi_bresp [1:0]
wire   i_npu_cfg_axi_arready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_arready
wire   [15:0] i_npu_cfg_axi_rid;         // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_rid [15:0]
wire   i_npu_cfg_axi_rvalid;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_rvalid
wire   [31:0] i_npu_cfg_axi_rdata;       // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_rdata [31:0]
wire   [1:0] i_npu_cfg_axi_rresp;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_rresp [1:0]
wire   i_npu_cfg_axi_rlast;              // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_rlast
wire   i_npu_cfg_axi_awready;            // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_awready
wire   i_npu_cfg_axi_wready;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_wready
wire   [15:0] i_npu_cfg_axi_bid;         // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_bid [15:0]
wire   i_npu_cfg_axi_bvalid;             // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_bvalid
wire   [1:0] i_npu_cfg_axi_bresp;        // core_archipelago > alb_mss_fab -- core_archipelago.npu_top.npu_cfg_axi_bresp [1:0]
wire   i_arcsync_axi_arready;            // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_arready
wire   [15:0] i_arcsync_axi_rid;         // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_rid [15:0]
wire   i_arcsync_axi_rvalid;             // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_rvalid
wire   [63:0] i_arcsync_axi_rdata;       // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_rdata [63:0]
wire   [1:0] i_arcsync_axi_rresp;        // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_rresp [1:0]
wire   i_arcsync_axi_rlast;              // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_rlast
wire   i_arcsync_axi_awready;            // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_awready
wire   i_arcsync_axi_wready;             // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_wready
wire   [15:0] i_arcsync_axi_bid;         // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_bid [15:0]
wire   i_arcsync_axi_bvalid;             // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_bvalid
wire   [1:0] i_arcsync_axi_bresp;        // core_archipelago > alb_mss_fab -- core_archipelago.arcsync_top.arcsync_axi_bresp [1:0]
wire   i_mss_mem_cmd_accept;             // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_cmd_accept
wire   i_mss_mem_rd_valid;               // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_rd_valid
wire   i_mss_mem_rd_excl_ok;             // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_rd_excl_ok
wire   [128-1:0] i_mss_mem_rd_data;      // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_rd_data [128-1:0]
wire   i_mss_mem_err_rd;                 // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_err_rd
wire   i_mss_mem_rd_last;                // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_rd_last
wire   i_mss_mem_wr_accept;              // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_wr_accept
wire   i_mss_mem_wr_done;                // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_wr_done
wire   i_mss_mem_wr_excl_done;           // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_wr_excl_done
wire   i_mss_mem_err_wr;                 // alb_mss_mem > alb_mss_fab -- alb_mss_mem.mss_mem_err_wr
wire   i_mss_mem_cmd_valid;              // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_valid
wire   i_mss_mem_cmd_read;               // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_read
wire   [32-1:0] i_mss_mem_cmd_addr;      // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_addr [32-1:0]
wire   i_mss_mem_cmd_wrap;               // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_wrap
wire   [2:0] i_mss_mem_cmd_data_size;    // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_data_size [2:0]
wire   [3:0] i_mss_mem_cmd_burst_size;   // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_burst_size [3:0]
wire   i_mss_mem_cmd_lock;               // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_lock
wire   i_mss_mem_cmd_excl;               // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_excl
wire   [1:0] i_mss_mem_cmd_prot;         // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_prot [1:0]
wire   [3:0] i_mss_mem_cmd_cache;        // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_cache [3:0]
wire   [8-1:0] i_mss_mem_cmd_id;         // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_id [8-1:0]
wire   [1-1:0] i_mss_mem_cmd_user;       // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_user [1-1:0]
wire   [1-1:0] i_mss_mem_cmd_region;     // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_cmd_region [1-1:0]
wire   i_mss_mem_rd_accept;              // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_rd_accept
wire   i_mss_mem_wr_valid;               // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_wr_valid
wire   [128-1:0] i_mss_mem_wr_data;      // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_wr_data [128-1:0]
wire   [128/8-1:0] i_mss_mem_wr_mask;    // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_wr_mask [128/8-1:0]
wire   i_mss_mem_wr_last;                // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_wr_last
wire   i_mss_mem_wr_resp_accept;         // alb_mss_fab > alb_mss_mem -- alb_mss_fab.mss_mem_wr_resp_accept
wire   i_mss_mem_dummy;                  // alb_mss_mem > unconnected -- alb_mss_mem.mss_mem_dummy

// Instantiation of module core_archipelago
core_archipelago icore_archipelago(
    .npu_core_clk                  (npu_core_clk)  // <   outside-of-hierarchy
  , .npu_core_rst_a                (npu_core_rst_a) // <   outside-of-hierarchy
  , .npu_noc_clk                   (npu_noc_clk)   // <   outside-of-hierarchy
  , .npu_noc_rst_a                 (npu_noc_rst_a) // <   outside-of-hierarchy
  , .npu_cfg_clk                   (npu_cfg_clk)   // <   outside-of-hierarchy
  , .npu_cfg_rst_a                 (npu_cfg_rst_a) // <   outside-of-hierarchy
  , .nl2arc0_wdt_clk               (nl2arc0_wdt_clk) // <   outside-of-hierarchy
  , .nl2arc1_wdt_clk               (nl2arc1_wdt_clk) // <   outside-of-hierarchy
  , .npu_csm_base                  (npu_csm_base)  // <   outside-of-hierarchy
  , .sl0_clk                       (sl0_clk)       // <   outside-of-hierarchy
  , .sl0_wdt_clk                   (sl0_wdt_clk)   // <   outside-of-hierarchy
  , .sl1_clk                       (sl1_clk)       // <   outside-of-hierarchy
  , .sl1_wdt_clk                   (sl1_wdt_clk)   // <   outside-of-hierarchy
  , .sl2_clk                       (sl2_clk)       // <   outside-of-hierarchy
  , .sl2_wdt_clk                   (sl2_wdt_clk)   // <   outside-of-hierarchy
  , .sl3_clk                       (sl3_clk)       // <   outside-of-hierarchy
  , .sl3_wdt_clk                   (sl3_wdt_clk)   // <   outside-of-hierarchy
  , .sl4_clk                       (sl4_clk)       // <   outside-of-hierarchy
  , .sl4_wdt_clk                   (sl4_wdt_clk)   // <   outside-of-hierarchy
  , .sl5_clk                       (sl5_clk)       // <   outside-of-hierarchy
  , .sl5_wdt_clk                   (sl5_wdt_clk)   // <   outside-of-hierarchy
  , .sl6_clk                       (sl6_clk)       // <   outside-of-hierarchy
  , .sl6_wdt_clk                   (sl6_wdt_clk)   // <   outside-of-hierarchy
  , .sl7_clk                       (sl7_clk)       // <   outside-of-hierarchy
  , .sl7_wdt_clk                   (sl7_wdt_clk)   // <   outside-of-hierarchy
  , .sl8_clk                       (sl8_clk)       // <   outside-of-hierarchy
  , .sl8_wdt_clk                   (sl8_wdt_clk)   // <   outside-of-hierarchy
  , .sl9_clk                       (sl9_clk)       // <   outside-of-hierarchy
  , .sl9_wdt_clk                   (sl9_wdt_clk)   // <   outside-of-hierarchy
  , .sl10_clk                      (sl10_clk)      // <   outside-of-hierarchy
  , .sl10_wdt_clk                  (sl10_wdt_clk)  // <   outside-of-hierarchy
  , .sl11_clk                      (sl11_clk)      // <   outside-of-hierarchy
  , .sl11_wdt_clk                  (sl11_wdt_clk)  // <   outside-of-hierarchy
  , .sl12_clk                      (sl12_clk)      // <   outside-of-hierarchy
  , .sl12_wdt_clk                  (sl12_wdt_clk)  // <   outside-of-hierarchy
  , .sl13_clk                      (sl13_clk)      // <   outside-of-hierarchy
  , .sl13_wdt_clk                  (sl13_wdt_clk)  // <   outside-of-hierarchy
  , .sl14_clk                      (sl14_clk)      // <   outside-of-hierarchy
  , .sl14_wdt_clk                  (sl14_wdt_clk)  // <   outside-of-hierarchy
  , .sl15_clk                      (sl15_clk)      // <   outside-of-hierarchy
  , .sl15_wdt_clk                  (sl15_wdt_clk)  // <   outside-of-hierarchy
  , .npu_mst0_axi_arready          (i_npu_mst0_axi_arready) // <   alb_mss_fab
  , .npu_mst0_axi_rvalid           (i_npu_mst0_axi_rvalid) // <   alb_mss_fab
  , .npu_mst0_axi_rid              (i_npu_mst0_axi_rid) // <   alb_mss_fab
  , .npu_mst0_axi_rdata            (i_npu_mst0_axi_rdata) // <   alb_mss_fab
  , .npu_mst0_axi_rresp            (i_npu_mst0_axi_rresp) // <   alb_mss_fab
  , .npu_mst0_axi_rlast            (i_npu_mst0_axi_rlast) // <   alb_mss_fab
  , .npu_mst0_axi_awready          (i_npu_mst0_axi_awready) // <   alb_mss_fab
  , .npu_mst0_axi_wready           (i_npu_mst0_axi_wready) // <   alb_mss_fab
  , .npu_mst0_axi_bvalid           (i_npu_mst0_axi_bvalid) // <   alb_mss_fab
  , .npu_mst0_axi_bid              (i_npu_mst0_axi_bid) // <   alb_mss_fab
  , .npu_mst0_axi_bresp            (i_npu_mst0_axi_bresp) // <   alb_mss_fab
  , .npu_mst1_axi_arready          (i_npu_mst1_axi_arready) // <   alb_mss_fab
  , .npu_mst1_axi_rvalid           (i_npu_mst1_axi_rvalid) // <   alb_mss_fab
  , .npu_mst1_axi_rid              (i_npu_mst1_axi_rid) // <   alb_mss_fab
  , .npu_mst1_axi_rdata            (i_npu_mst1_axi_rdata) // <   alb_mss_fab
  , .npu_mst1_axi_rresp            (i_npu_mst1_axi_rresp) // <   alb_mss_fab
  , .npu_mst1_axi_rlast            (i_npu_mst1_axi_rlast) // <   alb_mss_fab
  , .npu_mst1_axi_awready          (i_npu_mst1_axi_awready) // <   alb_mss_fab
  , .npu_mst1_axi_wready           (i_npu_mst1_axi_wready) // <   alb_mss_fab
  , .npu_mst1_axi_bvalid           (i_npu_mst1_axi_bvalid) // <   alb_mss_fab
  , .npu_mst1_axi_bid              (i_npu_mst1_axi_bid) // <   alb_mss_fab
  , .npu_mst1_axi_bresp            (i_npu_mst1_axi_bresp) // <   alb_mss_fab
  , .npu_mst2_axi_arready          (i_npu_mst2_axi_arready) // <   alb_mss_fab
  , .npu_mst2_axi_rvalid           (i_npu_mst2_axi_rvalid) // <   alb_mss_fab
  , .npu_mst2_axi_rid              (i_npu_mst2_axi_rid) // <   alb_mss_fab
  , .npu_mst2_axi_rdata            (i_npu_mst2_axi_rdata) // <   alb_mss_fab
  , .npu_mst2_axi_rresp            (i_npu_mst2_axi_rresp) // <   alb_mss_fab
  , .npu_mst2_axi_rlast            (i_npu_mst2_axi_rlast) // <   alb_mss_fab
  , .npu_mst2_axi_awready          (i_npu_mst2_axi_awready) // <   alb_mss_fab
  , .npu_mst2_axi_wready           (i_npu_mst2_axi_wready) // <   alb_mss_fab
  , .npu_mst2_axi_bvalid           (i_npu_mst2_axi_bvalid) // <   alb_mss_fab
  , .npu_mst2_axi_bid              (i_npu_mst2_axi_bid) // <   alb_mss_fab
  , .npu_mst2_axi_bresp            (i_npu_mst2_axi_bresp) // <   alb_mss_fab
  , .npu_mst3_axi_arready          (i_npu_mst3_axi_arready) // <   alb_mss_fab
  , .npu_mst3_axi_rvalid           (i_npu_mst3_axi_rvalid) // <   alb_mss_fab
  , .npu_mst3_axi_rid              (i_npu_mst3_axi_rid) // <   alb_mss_fab
  , .npu_mst3_axi_rdata            (i_npu_mst3_axi_rdata) // <   alb_mss_fab
  , .npu_mst3_axi_rresp            (i_npu_mst3_axi_rresp) // <   alb_mss_fab
  , .npu_mst3_axi_rlast            (i_npu_mst3_axi_rlast) // <   alb_mss_fab
  , .npu_mst3_axi_awready          (i_npu_mst3_axi_awready) // <   alb_mss_fab
  , .npu_mst3_axi_wready           (i_npu_mst3_axi_wready) // <   alb_mss_fab
  , .npu_mst3_axi_bvalid           (i_npu_mst3_axi_bvalid) // <   alb_mss_fab
  , .npu_mst3_axi_bid              (i_npu_mst3_axi_bid) // <   alb_mss_fab
  , .npu_mst3_axi_bresp            (i_npu_mst3_axi_bresp) // <   alb_mss_fab
  , .npu_mst4_axi_arready          (i_npu_mst4_axi_arready) // <   alb_mss_fab
  , .npu_mst4_axi_rvalid           (i_npu_mst4_axi_rvalid) // <   alb_mss_fab
  , .npu_mst4_axi_rid              (i_npu_mst4_axi_rid) // <   alb_mss_fab
  , .npu_mst4_axi_rdata            (i_npu_mst4_axi_rdata) // <   alb_mss_fab
  , .npu_mst4_axi_rresp            (i_npu_mst4_axi_rresp) // <   alb_mss_fab
  , .npu_mst4_axi_rlast            (i_npu_mst4_axi_rlast) // <   alb_mss_fab
  , .npu_mst4_axi_awready          (i_npu_mst4_axi_awready) // <   alb_mss_fab
  , .npu_mst4_axi_wready           (i_npu_mst4_axi_wready) // <   alb_mss_fab
  , .npu_mst4_axi_bvalid           (i_npu_mst4_axi_bvalid) // <   alb_mss_fab
  , .npu_mst4_axi_bid              (i_npu_mst4_axi_bid) // <   alb_mss_fab
  , .npu_mst4_axi_bresp            (i_npu_mst4_axi_bresp) // <   alb_mss_fab
  , .npu_dmi0_axi_arvalid          (i_npu_dmi0_axi_arvalid) // <   alb_mss_fab
  , .npu_dmi0_axi_arid             (i_npu_dmi0_axi_arid) // <   alb_mss_fab
  , .npu_dmi0_axi_araddr           (i_npu_dmi0_axi_araddr) // <   alb_mss_fab
  , .npu_dmi0_axi_arcache          (i_npu_dmi0_axi_arcache) // <   alb_mss_fab
  , .npu_dmi0_axi_arprot           (i_npu_dmi0_axi_arprot) // <   alb_mss_fab
  , .npu_dmi0_axi_arlock           (i_npu_dmi0_axi_arlock) // <   alb_mss_fab
  , .npu_dmi0_axi_arburst          (i_npu_dmi0_axi_arburst) // <   alb_mss_fab
  , .npu_dmi0_axi_arlen            (i_npu_dmi0_axi_arlen) // <   alb_mss_fab
  , .npu_dmi0_axi_arsize           (i_npu_dmi0_axi_arsize) // <   alb_mss_fab
  , .npu_dmi0_axi_rready           (i_npu_dmi0_axi_rready) // <   alb_mss_fab
  , .npu_dmi0_axi_awvalid          (i_npu_dmi0_axi_awvalid) // <   alb_mss_fab
  , .npu_dmi0_axi_awid             (i_npu_dmi0_axi_awid) // <   alb_mss_fab
  , .npu_dmi0_axi_awaddr           (i_npu_dmi0_axi_awaddr) // <   alb_mss_fab
  , .npu_dmi0_axi_awcache          (i_npu_dmi0_axi_awcache) // <   alb_mss_fab
  , .npu_dmi0_axi_awprot           (i_npu_dmi0_axi_awprot) // <   alb_mss_fab
  , .npu_dmi0_axi_awlock           (i_npu_dmi0_axi_awlock) // <   alb_mss_fab
  , .npu_dmi0_axi_awburst          (i_npu_dmi0_axi_awburst) // <   alb_mss_fab
  , .npu_dmi0_axi_awlen            (i_npu_dmi0_axi_awlen) // <   alb_mss_fab
  , .npu_dmi0_axi_awsize           (i_npu_dmi0_axi_awsize) // <   alb_mss_fab
  , .npu_dmi0_axi_wvalid           (i_npu_dmi0_axi_wvalid) // <   alb_mss_fab
  , .npu_dmi0_axi_wdata            (i_npu_dmi0_axi_wdata) // <   alb_mss_fab
  , .npu_dmi0_axi_wstrb            (i_npu_dmi0_axi_wstrb) // <   alb_mss_fab
  , .npu_dmi0_axi_wlast            (i_npu_dmi0_axi_wlast) // <   alb_mss_fab
  , .npu_dmi0_axi_bready           (i_npu_dmi0_axi_bready) // <   alb_mss_fab
  , .npu_cfg_axi_arvalid           (i_npu_cfg_axi_arvalid) // <   alb_mss_fab
  , .npu_cfg_axi_arid              (i_npu_cfg_axi_arid) // <   alb_mss_fab
  , .npu_cfg_axi_araddr            (i_npu_cfg_axi_araddr) // <   alb_mss_fab
  , .npu_cfg_axi_arcache           (i_npu_cfg_axi_arcache) // <   alb_mss_fab
  , .npu_cfg_axi_arprot            (i_npu_cfg_axi_arprot) // <   alb_mss_fab
  , .npu_cfg_axi_arlock            (i_npu_cfg_axi_arlock) // <   alb_mss_fab
  , .npu_cfg_axi_arburst           (i_npu_cfg_axi_arburst) // <   alb_mss_fab
  , .npu_cfg_axi_arlen             (i_npu_cfg_axi_arlen) // <   alb_mss_fab
  , .npu_cfg_axi_arsize            (i_npu_cfg_axi_arsize) // <   alb_mss_fab
  , .npu_cfg_axi_rready            (i_npu_cfg_axi_rready) // <   alb_mss_fab
  , .npu_cfg_axi_awvalid           (i_npu_cfg_axi_awvalid) // <   alb_mss_fab
  , .npu_cfg_axi_awid              (i_npu_cfg_axi_awid) // <   alb_mss_fab
  , .npu_cfg_axi_awaddr            (i_npu_cfg_axi_awaddr) // <   alb_mss_fab
  , .npu_cfg_axi_awcache           (i_npu_cfg_axi_awcache) // <   alb_mss_fab
  , .npu_cfg_axi_awprot            (i_npu_cfg_axi_awprot) // <   alb_mss_fab
  , .npu_cfg_axi_awlock            (i_npu_cfg_axi_awlock) // <   alb_mss_fab
  , .npu_cfg_axi_awburst           (i_npu_cfg_axi_awburst) // <   alb_mss_fab
  , .npu_cfg_axi_awlen             (i_npu_cfg_axi_awlen) // <   alb_mss_fab
  , .npu_cfg_axi_awsize            (i_npu_cfg_axi_awsize) // <   alb_mss_fab
  , .npu_cfg_axi_wvalid            (i_npu_cfg_axi_wvalid) // <   alb_mss_fab
  , .npu_cfg_axi_wdata             (i_npu_cfg_axi_wdata) // <   alb_mss_fab
  , .npu_cfg_axi_wstrb             (i_npu_cfg_axi_wstrb) // <   alb_mss_fab
  , .npu_cfg_axi_wlast             (i_npu_cfg_axi_wlast) // <   alb_mss_fab
  , .npu_cfg_axi_bready            (i_npu_cfg_axi_bready) // <   alb_mss_fab
  , .nl2arc_irq0_a                 (nl2arc_irq0_a) // <   outside-of-hierarchy
  , .nl2arc_irq1_a                 (nl2arc_irq1_a) // <   outside-of-hierarchy
  , .atclken                       (atclken)       // <   outside-of-hierarchy
  , .atresetn                      (atresetn)      // <   outside-of-hierarchy
  , .atb_cstimestamp               (atb_cstimestamp) // <   outside-of-hierarchy
  , .atready                       (atready)       // <   outside-of-hierarchy
  , .afvalid                       (afvalid)       // <   outside-of-hierarchy
  , .syncreq                       (syncreq)       // <   outside-of-hierarchy
  , .swe_atready                   (swe_atready)   // <   outside-of-hierarchy
  , .swe_afvalid                   (swe_afvalid)   // <   outside-of-hierarchy
  , .swe_syncreq                   (swe_syncreq)   // <   outside-of-hierarchy
  , .cti_trace_start               (cti_trace_start) // <   outside-of-hierarchy
  , .cti_trace_stop                (cti_trace_stop) // <   outside-of-hierarchy
  , .pclkdbg                       (pclkdbg)       // <   outside-of-hierarchy
  , .presetdbgn                    (presetdbgn)    // <   outside-of-hierarchy
  , .arct0_paddrdbg                (arct0_paddrdbg) // <   outside-of-hierarchy
  , .arct0_pseldbg                 (arct0_pseldbg) // <   outside-of-hierarchy
  , .arct0_penabledbg              (arct0_penabledbg) // <   outside-of-hierarchy
  , .arct0_pwritedbg               (arct0_pwritedbg) // <   outside-of-hierarchy
  , .arct0_pwdatadbg               (arct0_pwdatadbg) // <   outside-of-hierarchy
  , .arct0_dbgen                   (arct0_dbgen)   // <   outside-of-hierarchy
  , .arct0_niden                   (arct0_niden)   // <   outside-of-hierarchy
  , .sl0nl1arc_niden               (sl0nl1arc_niden) // <   outside-of-hierarchy
  , .sl0nl1arc_dbgen               (sl0nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl1nl1arc_niden               (sl1nl1arc_niden) // <   outside-of-hierarchy
  , .sl1nl1arc_dbgen               (sl1nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl2nl1arc_niden               (sl2nl1arc_niden) // <   outside-of-hierarchy
  , .sl2nl1arc_dbgen               (sl2nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl3nl1arc_niden               (sl3nl1arc_niden) // <   outside-of-hierarchy
  , .sl3nl1arc_dbgen               (sl3nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl4nl1arc_niden               (sl4nl1arc_niden) // <   outside-of-hierarchy
  , .sl4nl1arc_dbgen               (sl4nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl5nl1arc_niden               (sl5nl1arc_niden) // <   outside-of-hierarchy
  , .sl5nl1arc_dbgen               (sl5nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl6nl1arc_niden               (sl6nl1arc_niden) // <   outside-of-hierarchy
  , .sl6nl1arc_dbgen               (sl6nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl7nl1arc_niden               (sl7nl1arc_niden) // <   outside-of-hierarchy
  , .sl7nl1arc_dbgen               (sl7nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl8nl1arc_niden               (sl8nl1arc_niden) // <   outside-of-hierarchy
  , .sl8nl1arc_dbgen               (sl8nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl9nl1arc_niden               (sl9nl1arc_niden) // <   outside-of-hierarchy
  , .sl9nl1arc_dbgen               (sl9nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl10nl1arc_niden              (sl10nl1arc_niden) // <   outside-of-hierarchy
  , .sl10nl1arc_dbgen              (sl10nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl11nl1arc_niden              (sl11nl1arc_niden) // <   outside-of-hierarchy
  , .sl11nl1arc_dbgen              (sl11nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl12nl1arc_niden              (sl12nl1arc_niden) // <   outside-of-hierarchy
  , .sl12nl1arc_dbgen              (sl12nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl13nl1arc_niden              (sl13nl1arc_niden) // <   outside-of-hierarchy
  , .sl13nl1arc_dbgen              (sl13nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl14nl1arc_niden              (sl14nl1arc_niden) // <   outside-of-hierarchy
  , .sl14nl1arc_dbgen              (sl14nl1arc_dbgen) // <   outside-of-hierarchy
  , .sl15nl1arc_niden              (sl15nl1arc_niden) // <   outside-of-hierarchy
  , .sl15nl1arc_dbgen              (sl15nl1arc_dbgen) // <   outside-of-hierarchy
  , .nl2arc0_dbgen                 (nl2arc0_dbgen) // <   outside-of-hierarchy
  , .nl2arc0_niden                 (nl2arc0_niden) // <   outside-of-hierarchy
  , .nl2arc1_dbgen                 (nl2arc1_dbgen) // <   outside-of-hierarchy
  , .nl2arc1_niden                 (nl2arc1_niden) // <   outside-of-hierarchy
  , .test_mode                     (test_mode)     // <   outside-of-hierarchy
  , .arcsync_axi_arvalid           (i_arcsync_axi_arvalid) // <   alb_mss_fab
  , .arcsync_axi_arid              (i_arcsync_axi_arid) // <   alb_mss_fab
  , .arcsync_axi_araddr            (i_arcsync_axi_araddr) // <   alb_mss_fab
  , .arcsync_axi_arcache           (i_arcsync_axi_arcache) // <   alb_mss_fab
  , .arcsync_axi_arprot            (i_arcsync_axi_arprot) // <   alb_mss_fab
  , .arcsync_axi_arlock            (i_arcsync_axi_arlock) // <   alb_mss_fab
  , .arcsync_axi_arburst           (i_arcsync_axi_arburst) // <   alb_mss_fab
  , .arcsync_axi_arlen             (i_arcsync_axi_arlen) // <   alb_mss_fab
  , .arcsync_axi_arsize            (i_arcsync_axi_arsize) // <   alb_mss_fab
  , .arcsync_axi_rready            (i_arcsync_axi_rready) // <   alb_mss_fab
  , .arcsync_axi_awvalid           (i_arcsync_axi_awvalid) // <   alb_mss_fab
  , .arcsync_axi_awid              (i_arcsync_axi_awid) // <   alb_mss_fab
  , .arcsync_axi_awaddr            (i_arcsync_axi_awaddr) // <   alb_mss_fab
  , .arcsync_axi_awcache           (i_arcsync_axi_awcache) // <   alb_mss_fab
  , .arcsync_axi_awprot            (i_arcsync_axi_awprot) // <   alb_mss_fab
  , .arcsync_axi_awlock            (i_arcsync_axi_awlock) // <   alb_mss_fab
  , .arcsync_axi_awburst           (i_arcsync_axi_awburst) // <   alb_mss_fab
  , .arcsync_axi_awlen             (i_arcsync_axi_awlen) // <   alb_mss_fab
  , .arcsync_axi_awsize            (i_arcsync_axi_awsize) // <   alb_mss_fab
  , .arcsync_axi_wvalid            (i_arcsync_axi_wvalid) // <   alb_mss_fab
  , .arcsync_axi_wdata             (i_arcsync_axi_wdata) // <   alb_mss_fab
  , .arcsync_axi_wstrb             (i_arcsync_axi_wstrb) // <   alb_mss_fab
  , .arcsync_axi_wlast             (i_arcsync_axi_wlast) // <   alb_mss_fab
  , .arcsync_axi_bready            (i_arcsync_axi_bready) // <   alb_mss_fab
  , .nl2arc0_ext_arc_halt_req_a    (nl2arc0_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .nl2arc0_ext_arc_run_req_a     (nl2arc0_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .nl2arc1_ext_arc_halt_req_a    (nl2arc1_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .nl2arc1_ext_arc_run_req_a     (nl2arc1_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl0nl1arc_ext_arc_halt_req_a  (sl0nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl0nl1arc_ext_arc_run_req_a   (sl0nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl1nl1arc_ext_arc_halt_req_a  (sl1nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl1nl1arc_ext_arc_run_req_a   (sl1nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl2nl1arc_ext_arc_halt_req_a  (sl2nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl2nl1arc_ext_arc_run_req_a   (sl2nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl3nl1arc_ext_arc_halt_req_a  (sl3nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl3nl1arc_ext_arc_run_req_a   (sl3nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl4nl1arc_ext_arc_halt_req_a  (sl4nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl4nl1arc_ext_arc_run_req_a   (sl4nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl5nl1arc_ext_arc_halt_req_a  (sl5nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl5nl1arc_ext_arc_run_req_a   (sl5nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl6nl1arc_ext_arc_halt_req_a  (sl6nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl6nl1arc_ext_arc_run_req_a   (sl6nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl7nl1arc_ext_arc_halt_req_a  (sl7nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl7nl1arc_ext_arc_run_req_a   (sl7nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl8nl1arc_ext_arc_halt_req_a  (sl8nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl8nl1arc_ext_arc_run_req_a   (sl8nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl9nl1arc_ext_arc_halt_req_a  (sl9nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl9nl1arc_ext_arc_run_req_a   (sl9nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl10nl1arc_ext_arc_halt_req_a (sl10nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl10nl1arc_ext_arc_run_req_a  (sl10nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl11nl1arc_ext_arc_halt_req_a (sl11nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl11nl1arc_ext_arc_run_req_a  (sl11nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl12nl1arc_ext_arc_halt_req_a (sl12nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl12nl1arc_ext_arc_run_req_a  (sl12nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl13nl1arc_ext_arc_halt_req_a (sl13nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl13nl1arc_ext_arc_run_req_a  (sl13nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl14nl1arc_ext_arc_halt_req_a (sl14nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl14nl1arc_ext_arc_run_req_a  (sl14nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .sl15nl1arc_ext_arc_halt_req_a (sl15nl1arc_ext_arc_halt_req_a) // <   outside-of-hierarchy
  , .sl15nl1arc_ext_arc_run_req_a  (sl15nl1arc_ext_arc_run_req_a) // <   outside-of-hierarchy
  , .v0c0arc_halt_ack_a            (i_v0c0arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c0ext_arc_halt_req_a        (i_v0c0ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c0arc_run_ack_a             (i_v0c0arc_run_ack_a) // <   arcsync_top_stub
  , .v0c0ext_arc_run_req_a         (i_v0c0ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c0sys_sleep_r               (i_v0c0sys_sleep_r) // <   arcsync_top_stub
  , .v0c0sys_sleep_mode_r          (i_v0c0sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c0sys_halt_r                (i_v0c0sys_halt_r) // <   arcsync_top_stub
  , .v0c0sys_tf_halt_r             (i_v0c0sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c0pmode                     (i_v0c0pmode)   // <   arcsync_top_stub
  , .v0c1arc_halt_ack_a            (i_v0c1arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c1ext_arc_halt_req_a        (i_v0c1ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c1arc_run_ack_a             (i_v0c1arc_run_ack_a) // <   arcsync_top_stub
  , .v0c1ext_arc_run_req_a         (i_v0c1ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c1sys_sleep_r               (i_v0c1sys_sleep_r) // <   arcsync_top_stub
  , .v0c1sys_sleep_mode_r          (i_v0c1sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c1sys_halt_r                (i_v0c1sys_halt_r) // <   arcsync_top_stub
  , .v0c1sys_tf_halt_r             (i_v0c1sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c1pmode                     (i_v0c1pmode)   // <   arcsync_top_stub
  , .v0c2arc_halt_ack_a            (i_v0c2arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c2ext_arc_halt_req_a        (i_v0c2ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c2arc_run_ack_a             (i_v0c2arc_run_ack_a) // <   arcsync_top_stub
  , .v0c2ext_arc_run_req_a         (i_v0c2ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c2sys_sleep_r               (i_v0c2sys_sleep_r) // <   arcsync_top_stub
  , .v0c2sys_sleep_mode_r          (i_v0c2sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c2sys_halt_r                (i_v0c2sys_halt_r) // <   arcsync_top_stub
  , .v0c2sys_tf_halt_r             (i_v0c2sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c2pmode                     (i_v0c2pmode)   // <   arcsync_top_stub
  , .v0c3arc_halt_ack_a            (i_v0c3arc_halt_ack_a) // <   arcsync_top_stub
  , .v0c3ext_arc_halt_req_a        (i_v0c3ext_arc_halt_req_a) // <   arcsync_top_stub
  , .v0c3arc_run_ack_a             (i_v0c3arc_run_ack_a) // <   arcsync_top_stub
  , .v0c3ext_arc_run_req_a         (i_v0c3ext_arc_run_req_a) // <   arcsync_top_stub
  , .v0c3sys_sleep_r               (i_v0c3sys_sleep_r) // <   arcsync_top_stub
  , .v0c3sys_sleep_mode_r          (i_v0c3sys_sleep_mode_r) // <   arcsync_top_stub
  , .v0c3sys_halt_r                (i_v0c3sys_halt_r) // <   arcsync_top_stub
  , .v0c3sys_tf_halt_r             (i_v0c3sys_tf_halt_r) // <   arcsync_top_stub
  , .v0c3pmode                     (i_v0c3pmode)   // <   arcsync_top_stub
  , .arcsync_axi_clk               (arcsync_axi_clk) // <   outside-of-hierarchy
  , .arcsync_axi_rst_a             (arcsync_axi_rst_a) // <   outside-of-hierarchy
  , .arcsync_core_iso_override     (arcsync_core_iso_override) // <   outside-of-hierarchy
  , .arcsync_clk                   (arcsync_clk)   // <   outside-of-hierarchy
  , .arcsync_rst_a                 (arcsync_rst_a) // <   outside-of-hierarchy
  , .nl2arc_isolate_n              (i_nl2arc_isolate_n) //   > arcsync_top_stub
  , .nl2arc_isolate                (i_nl2arc_isolate) //   > arcsync_top_stub
  , .nl2arc_pd_mem                 (i_nl2arc_pd_mem) //   > arcsync_top_stub
  , .nl2arc_pd_logic               (i_nl2arc_pd_logic) //   > arcsync_top_stub
  , .nl2arc_pd_logic1              (i_nl2arc_pd_logic1) //   > arcsync_top_stub
  , .nl2arc_pd_logic2              (i_nl2arc_pd_logic2) //   > arcsync_top_stub
  , .grp0_isolate_n                (i_grp0_isolate_n) //   > arcsync_top_stub
  , .grp0_isolate                  (i_grp0_isolate) //   > arcsync_top_stub
  , .grp0_pd_mem                   (i_grp0_pd_mem) //   > arcsync_top_stub
  , .grp0_pd_logic                 (i_grp0_pd_logic) //   > arcsync_top_stub
  , .grp0_pd_logic1                (i_grp0_pd_logic1) //   > arcsync_top_stub
  , .grp0_pd_logic2                (i_grp0_pd_logic2) //   > arcsync_top_stub
  , .grp1_isolate_n                (i_grp1_isolate_n) //   > arcsync_top_stub
  , .grp1_isolate                  (i_grp1_isolate) //   > arcsync_top_stub
  , .grp1_pd_mem                   (i_grp1_pd_mem) //   > arcsync_top_stub
  , .grp1_pd_logic                 (i_grp1_pd_logic) //   > arcsync_top_stub
  , .grp1_pd_logic1                (i_grp1_pd_logic1) //   > arcsync_top_stub
  , .grp1_pd_logic2                (i_grp1_pd_logic2) //   > arcsync_top_stub
  , .grp2_isolate_n                (i_grp2_isolate_n) //   > arcsync_top_stub
  , .grp2_isolate                  (i_grp2_isolate) //   > arcsync_top_stub
  , .grp2_pd_mem                   (i_grp2_pd_mem) //   > arcsync_top_stub
  , .grp2_pd_logic                 (i_grp2_pd_logic) //   > arcsync_top_stub
  , .grp2_pd_logic1                (i_grp2_pd_logic1) //   > arcsync_top_stub
  , .grp2_pd_logic2                (i_grp2_pd_logic2) //   > arcsync_top_stub
  , .grp3_isolate_n                (i_grp3_isolate_n) //   > arcsync_top_stub
  , .grp3_isolate                  (i_grp3_isolate) //   > arcsync_top_stub
  , .grp3_pd_mem                   (i_grp3_pd_mem) //   > arcsync_top_stub
  , .grp3_pd_logic                 (i_grp3_pd_logic) //   > arcsync_top_stub
  , .grp3_pd_logic1                (i_grp3_pd_logic1) //   > arcsync_top_stub
  , .grp3_pd_logic2                (i_grp3_pd_logic2) //   > arcsync_top_stub
  , .sl0nl1arc_isolate_n           (i_sl0nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl0nl1arc_isolate             (i_sl0nl1arc_isolate) //   > arcsync_top_stub
  , .sl0nl1arc_pd_mem              (i_sl0nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl0nl1arc_pd_logic            (i_sl0nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl0nl1arc_pd_logic1           (i_sl0nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl0nl1arc_pd_logic2           (i_sl0nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl1nl1arc_isolate_n           (i_sl1nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl1nl1arc_isolate             (i_sl1nl1arc_isolate) //   > arcsync_top_stub
  , .sl1nl1arc_pd_mem              (i_sl1nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl1nl1arc_pd_logic            (i_sl1nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl1nl1arc_pd_logic1           (i_sl1nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl1nl1arc_pd_logic2           (i_sl1nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl2nl1arc_isolate_n           (i_sl2nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl2nl1arc_isolate             (i_sl2nl1arc_isolate) //   > arcsync_top_stub
  , .sl2nl1arc_pd_mem              (i_sl2nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl2nl1arc_pd_logic            (i_sl2nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl2nl1arc_pd_logic1           (i_sl2nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl2nl1arc_pd_logic2           (i_sl2nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl3nl1arc_isolate_n           (i_sl3nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl3nl1arc_isolate             (i_sl3nl1arc_isolate) //   > arcsync_top_stub
  , .sl3nl1arc_pd_mem              (i_sl3nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl3nl1arc_pd_logic            (i_sl3nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl3nl1arc_pd_logic1           (i_sl3nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl3nl1arc_pd_logic2           (i_sl3nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl4nl1arc_isolate_n           (i_sl4nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl4nl1arc_isolate             (i_sl4nl1arc_isolate) //   > arcsync_top_stub
  , .sl4nl1arc_pd_mem              (i_sl4nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl4nl1arc_pd_logic            (i_sl4nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl4nl1arc_pd_logic1           (i_sl4nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl4nl1arc_pd_logic2           (i_sl4nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl5nl1arc_isolate_n           (i_sl5nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl5nl1arc_isolate             (i_sl5nl1arc_isolate) //   > arcsync_top_stub
  , .sl5nl1arc_pd_mem              (i_sl5nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl5nl1arc_pd_logic            (i_sl5nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl5nl1arc_pd_logic1           (i_sl5nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl5nl1arc_pd_logic2           (i_sl5nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl6nl1arc_isolate_n           (i_sl6nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl6nl1arc_isolate             (i_sl6nl1arc_isolate) //   > arcsync_top_stub
  , .sl6nl1arc_pd_mem              (i_sl6nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl6nl1arc_pd_logic            (i_sl6nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl6nl1arc_pd_logic1           (i_sl6nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl6nl1arc_pd_logic2           (i_sl6nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl7nl1arc_isolate_n           (i_sl7nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl7nl1arc_isolate             (i_sl7nl1arc_isolate) //   > arcsync_top_stub
  , .sl7nl1arc_pd_mem              (i_sl7nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl7nl1arc_pd_logic            (i_sl7nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl7nl1arc_pd_logic1           (i_sl7nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl7nl1arc_pd_logic2           (i_sl7nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl8nl1arc_isolate_n           (i_sl8nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl8nl1arc_isolate             (i_sl8nl1arc_isolate) //   > arcsync_top_stub
  , .sl8nl1arc_pd_mem              (i_sl8nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl8nl1arc_pd_logic            (i_sl8nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl8nl1arc_pd_logic1           (i_sl8nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl8nl1arc_pd_logic2           (i_sl8nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl9nl1arc_isolate_n           (i_sl9nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl9nl1arc_isolate             (i_sl9nl1arc_isolate) //   > arcsync_top_stub
  , .sl9nl1arc_pd_mem              (i_sl9nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl9nl1arc_pd_logic            (i_sl9nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl9nl1arc_pd_logic1           (i_sl9nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl9nl1arc_pd_logic2           (i_sl9nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl10nl1arc_isolate_n          (i_sl10nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl10nl1arc_isolate            (i_sl10nl1arc_isolate) //   > arcsync_top_stub
  , .sl10nl1arc_pd_mem             (i_sl10nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl10nl1arc_pd_logic           (i_sl10nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl10nl1arc_pd_logic1          (i_sl10nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl10nl1arc_pd_logic2          (i_sl10nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl11nl1arc_isolate_n          (i_sl11nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl11nl1arc_isolate            (i_sl11nl1arc_isolate) //   > arcsync_top_stub
  , .sl11nl1arc_pd_mem             (i_sl11nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl11nl1arc_pd_logic           (i_sl11nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl11nl1arc_pd_logic1          (i_sl11nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl11nl1arc_pd_logic2          (i_sl11nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl12nl1arc_isolate_n          (i_sl12nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl12nl1arc_isolate            (i_sl12nl1arc_isolate) //   > arcsync_top_stub
  , .sl12nl1arc_pd_mem             (i_sl12nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl12nl1arc_pd_logic           (i_sl12nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl12nl1arc_pd_logic1          (i_sl12nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl12nl1arc_pd_logic2          (i_sl12nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl13nl1arc_isolate_n          (i_sl13nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl13nl1arc_isolate            (i_sl13nl1arc_isolate) //   > arcsync_top_stub
  , .sl13nl1arc_pd_mem             (i_sl13nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl13nl1arc_pd_logic           (i_sl13nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl13nl1arc_pd_logic1          (i_sl13nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl13nl1arc_pd_logic2          (i_sl13nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl14nl1arc_isolate_n          (i_sl14nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl14nl1arc_isolate            (i_sl14nl1arc_isolate) //   > arcsync_top_stub
  , .sl14nl1arc_pd_mem             (i_sl14nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl14nl1arc_pd_logic           (i_sl14nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl14nl1arc_pd_logic1          (i_sl14nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl14nl1arc_pd_logic2          (i_sl14nl1arc_pd_logic2) //   > arcsync_top_stub
  , .sl15nl1arc_isolate_n          (i_sl15nl1arc_isolate_n) //   > arcsync_top_stub
  , .sl15nl1arc_isolate            (i_sl15nl1arc_isolate) //   > arcsync_top_stub
  , .sl15nl1arc_pd_mem             (i_sl15nl1arc_pd_mem) //   > arcsync_top_stub
  , .sl15nl1arc_pd_logic           (i_sl15nl1arc_pd_logic) //   > arcsync_top_stub
  , .sl15nl1arc_pd_logic1          (i_sl15nl1arc_pd_logic1) //   > arcsync_top_stub
  , .sl15nl1arc_pd_logic2          (i_sl15nl1arc_pd_logic2) //   > arcsync_top_stub
  , .v0csm_addr_base               (i_v0csm_addr_base) //   > arcsync_top_stub
  , .v0periph_addr_base            (i_v0periph_addr_base) //   > arcsync_top_stub
  , .v0clusternum                  (i_v0clusternum) //   > arcsync_top_stub
  , .v0c0arcnum                    (i_v0c0arcnum)  //   > arcsync_top_stub
  , .v0c0intvbase                  (i_v0c0intvbase) //   > arcsync_top_stub
  , .v0c0rst_a                     (i_v0c0rst_a)   //   > arcsync_top_stub
  , .v0c0clk_en                    (i_v0c0clk_en)  //   > arcsync_top_stub
  , .v0c0arc_halt_req              (i_v0c0arc_halt_req) //   > arcsync_top_stub
  , .v0c0ext_arc_halt_ack          (i_v0c0ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c0arc_run_req               (i_v0c0arc_run_req) //   > arcsync_top_stub
  , .v0c0ext_arc_run_ack           (i_v0c0ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c0arc_irq0_a                (i_v0c0arc_irq0_a) //   > arcsync_top_stub
  , .v0c0arc_irq1_a                (i_v0c0arc_irq1_a) //   > arcsync_top_stub
  , .v0c0arc_event0_a              (i_v0c0arc_event0_a) //   > arcsync_top_stub
  , .v0c0arc_event1_a              (i_v0c0arc_event1_a) //   > arcsync_top_stub
  , .v0c1arcnum                    (i_v0c1arcnum)  //   > arcsync_top_stub
  , .v0c1intvbase                  (i_v0c1intvbase) //   > arcsync_top_stub
  , .v0c1rst_a                     (i_v0c1rst_a)   //   > arcsync_top_stub
  , .v0c1clk_en                    (i_v0c1clk_en)  //   > arcsync_top_stub
  , .v0c1arc_halt_req              (i_v0c1arc_halt_req) //   > arcsync_top_stub
  , .v0c1ext_arc_halt_ack          (i_v0c1ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c1arc_run_req               (i_v0c1arc_run_req) //   > arcsync_top_stub
  , .v0c1ext_arc_run_ack           (i_v0c1ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c1arc_irq0_a                (i_v0c1arc_irq0_a) //   > arcsync_top_stub
  , .v0c1arc_irq1_a                (i_v0c1arc_irq1_a) //   > arcsync_top_stub
  , .v0c1arc_event0_a              (i_v0c1arc_event0_a) //   > arcsync_top_stub
  , .v0c1arc_event1_a              (i_v0c1arc_event1_a) //   > arcsync_top_stub
  , .v0c2arcnum                    (i_v0c2arcnum)  //   > arcsync_top_stub
  , .v0c2intvbase                  (i_v0c2intvbase) //   > arcsync_top_stub
  , .v0c2rst_a                     (i_v0c2rst_a)   //   > arcsync_top_stub
  , .v0c2clk_en                    (i_v0c2clk_en)  //   > arcsync_top_stub
  , .v0c2arc_halt_req              (i_v0c2arc_halt_req) //   > arcsync_top_stub
  , .v0c2ext_arc_halt_ack          (i_v0c2ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c2arc_run_req               (i_v0c2arc_run_req) //   > arcsync_top_stub
  , .v0c2ext_arc_run_ack           (i_v0c2ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c2arc_irq0_a                (i_v0c2arc_irq0_a) //   > arcsync_top_stub
  , .v0c2arc_irq1_a                (i_v0c2arc_irq1_a) //   > arcsync_top_stub
  , .v0c2arc_event0_a              (i_v0c2arc_event0_a) //   > arcsync_top_stub
  , .v0c2arc_event1_a              (i_v0c2arc_event1_a) //   > arcsync_top_stub
  , .v0c3arcnum                    (i_v0c3arcnum)  //   > arcsync_top_stub
  , .v0c3intvbase                  (i_v0c3intvbase) //   > arcsync_top_stub
  , .v0c3rst_a                     (i_v0c3rst_a)   //   > arcsync_top_stub
  , .v0c3clk_en                    (i_v0c3clk_en)  //   > arcsync_top_stub
  , .v0c3arc_halt_req              (i_v0c3arc_halt_req) //   > arcsync_top_stub
  , .v0c3ext_arc_halt_ack          (i_v0c3ext_arc_halt_ack) //   > arcsync_top_stub
  , .v0c3arc_run_req               (i_v0c3arc_run_req) //   > arcsync_top_stub
  , .v0c3ext_arc_run_ack           (i_v0c3ext_arc_run_ack) //   > arcsync_top_stub
  , .v0c3arc_irq0_a                (i_v0c3arc_irq0_a) //   > arcsync_top_stub
  , .v0c3arc_irq1_a                (i_v0c3arc_irq1_a) //   > arcsync_top_stub
  , .v0c3arc_event0_a              (i_v0c3arc_event0_a) //   > arcsync_top_stub
  , .v0c3arc_event1_a              (i_v0c3arc_event1_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_irq0_a             (i_vpx_v0_vm0_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_irq_ac_a           (i_vpx_v0_vm0_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_evt0_a             (i_vpx_v0_vm0_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm0_evt_ac_a           (i_vpx_v0_vm0_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_irq0_a             (i_vpx_v0_vm1_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_irq_ac_a           (i_vpx_v0_vm1_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_evt0_a             (i_vpx_v0_vm1_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm1_evt_ac_a           (i_vpx_v0_vm1_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_irq0_a             (i_vpx_v0_vm2_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_irq_ac_a           (i_vpx_v0_vm2_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_evt0_a             (i_vpx_v0_vm2_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm2_evt_ac_a           (i_vpx_v0_vm2_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_irq0_a             (i_vpx_v0_vm3_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_irq_ac_a           (i_vpx_v0_vm3_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_evt0_a             (i_vpx_v0_vm3_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm3_evt_ac_a           (i_vpx_v0_vm3_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_irq0_a             (i_vpx_v0_vm4_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_irq_ac_a           (i_vpx_v0_vm4_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_evt0_a             (i_vpx_v0_vm4_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm4_evt_ac_a           (i_vpx_v0_vm4_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_irq0_a             (i_vpx_v0_vm5_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_irq_ac_a           (i_vpx_v0_vm5_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_evt0_a             (i_vpx_v0_vm5_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm5_evt_ac_a           (i_vpx_v0_vm5_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_irq0_a             (i_vpx_v0_vm6_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_irq_ac_a           (i_vpx_v0_vm6_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_evt0_a             (i_vpx_v0_vm6_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm6_evt_ac_a           (i_vpx_v0_vm6_evt_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_irq0_a             (i_vpx_v0_vm7_irq0_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_irq_ac_a           (i_vpx_v0_vm7_irq_ac_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_evt0_a             (i_vpx_v0_vm7_evt0_a) //   > arcsync_top_stub
  , .vpx_v0_vm7_evt_ac_a           (i_vpx_v0_vm7_evt_ac_a) //   > arcsync_top_stub
  , .v0c0_isolate_n                (i_v0c0_isolate_n) //   > arcsync_top_stub
  , .v0c0_isolate                  (i_v0c0_isolate) //   > arcsync_top_stub
  , .v0c0_pd_mem                   (i_v0c0_pd_mem) //   > arcsync_top_stub
  , .v0c0_pd_logic                 (i_v0c0_pd_logic) //   > arcsync_top_stub
  , .v0c0_pd_logic1                (i_v0c0_pd_logic1) //   > arcsync_top_stub
  , .v0c0_pd_logic2                (i_v0c0_pd_logic2) //   > arcsync_top_stub
  , .v0c1_isolate_n                (i_v0c1_isolate_n) //   > arcsync_top_stub
  , .v0c1_isolate                  (i_v0c1_isolate) //   > arcsync_top_stub
  , .v0c1_pd_mem                   (i_v0c1_pd_mem) //   > arcsync_top_stub
  , .v0c1_pd_logic                 (i_v0c1_pd_logic) //   > arcsync_top_stub
  , .v0c1_pd_logic1                (i_v0c1_pd_logic1) //   > arcsync_top_stub
  , .v0c1_pd_logic2                (i_v0c1_pd_logic2) //   > arcsync_top_stub
  , .v0c2_isolate_n                (i_v0c2_isolate_n) //   > arcsync_top_stub
  , .v0c2_isolate                  (i_v0c2_isolate) //   > arcsync_top_stub
  , .v0c2_pd_mem                   (i_v0c2_pd_mem) //   > arcsync_top_stub
  , .v0c2_pd_logic                 (i_v0c2_pd_logic) //   > arcsync_top_stub
  , .v0c2_pd_logic1                (i_v0c2_pd_logic1) //   > arcsync_top_stub
  , .v0c2_pd_logic2                (i_v0c2_pd_logic2) //   > arcsync_top_stub
  , .v0c3_isolate_n                (i_v0c3_isolate_n) //   > arcsync_top_stub
  , .v0c3_isolate                  (i_v0c3_isolate) //   > arcsync_top_stub
  , .v0c3_pd_mem                   (i_v0c3_pd_mem) //   > arcsync_top_stub
  , .v0c3_pd_logic                 (i_v0c3_pd_logic) //   > arcsync_top_stub
  , .v0c3_pd_logic1                (i_v0c3_pd_logic1) //   > arcsync_top_stub
  , .v0c3_pd_logic2                (i_v0c3_pd_logic2) //   > arcsync_top_stub
  , .npu_mst0_axi_arid             (i_npu_mst0_axi_arid) //   > alb_mss_fab
  , .npu_mst0_axi_arvalid          (i_npu_mst0_axi_arvalid) //   > alb_mss_fab
  , .npu_mst0_axi_araddr           (i_npu_mst0_axi_araddr) //   > alb_mss_fab
  , .npu_mst0_axi_arburst          (i_npu_mst0_axi_arburst) //   > alb_mss_fab
  , .npu_mst0_axi_arsize           (i_npu_mst0_axi_arsize) //   > alb_mss_fab
  , .npu_mst0_axi_arlock           (i_npu_mst0_axi_arlock) //   > alb_mss_fab
  , .npu_mst0_axi_arlen            (i_npu_mst0_axi_arlen) //   > alb_mss_fab
  , .npu_mst0_axi_arcache          (i_npu_mst0_axi_arcache) //   > alb_mss_fab
  , .npu_mst0_axi_arprot           (i_npu_mst0_axi_arprot) //   > alb_mss_fab
  , .npu_mst0_axi_rready           (i_npu_mst0_axi_rready) //   > alb_mss_fab
  , .npu_mst0_axi_awid             (i_npu_mst0_axi_awid) //   > alb_mss_fab
  , .npu_mst0_axi_awvalid          (i_npu_mst0_axi_awvalid) //   > alb_mss_fab
  , .npu_mst0_axi_awaddr           (i_npu_mst0_axi_awaddr) //   > alb_mss_fab
  , .npu_mst0_axi_awburst          (i_npu_mst0_axi_awburst) //   > alb_mss_fab
  , .npu_mst0_axi_awsize           (i_npu_mst0_axi_awsize) //   > alb_mss_fab
  , .npu_mst0_axi_awlock           (i_npu_mst0_axi_awlock) //   > alb_mss_fab
  , .npu_mst0_axi_awlen            (i_npu_mst0_axi_awlen) //   > alb_mss_fab
  , .npu_mst0_axi_awcache          (i_npu_mst0_axi_awcache) //   > alb_mss_fab
  , .npu_mst0_axi_awprot           (i_npu_mst0_axi_awprot) //   > alb_mss_fab
  , .npu_mst0_axi_wvalid           (i_npu_mst0_axi_wvalid) //   > alb_mss_fab
  , .npu_mst0_axi_wdata            (i_npu_mst0_axi_wdata) //   > alb_mss_fab
  , .npu_mst0_axi_wstrb            (i_npu_mst0_axi_wstrb) //   > alb_mss_fab
  , .npu_mst0_axi_wlast            (i_npu_mst0_axi_wlast) //   > alb_mss_fab
  , .npu_mst0_axi_bready           (i_npu_mst0_axi_bready) //   > alb_mss_fab
  , .npu_mst1_axi_arid             (i_npu_mst1_axi_arid) //   > alb_mss_fab
  , .npu_mst1_axi_arvalid          (i_npu_mst1_axi_arvalid) //   > alb_mss_fab
  , .npu_mst1_axi_araddr           (i_npu_mst1_axi_araddr) //   > alb_mss_fab
  , .npu_mst1_axi_arburst          (i_npu_mst1_axi_arburst) //   > alb_mss_fab
  , .npu_mst1_axi_arsize           (i_npu_mst1_axi_arsize) //   > alb_mss_fab
  , .npu_mst1_axi_arlock           (i_npu_mst1_axi_arlock) //   > alb_mss_fab
  , .npu_mst1_axi_arlen            (i_npu_mst1_axi_arlen) //   > alb_mss_fab
  , .npu_mst1_axi_arcache          (i_npu_mst1_axi_arcache) //   > alb_mss_fab
  , .npu_mst1_axi_arprot           (i_npu_mst1_axi_arprot) //   > alb_mss_fab
  , .npu_mst1_axi_rready           (i_npu_mst1_axi_rready) //   > alb_mss_fab
  , .npu_mst1_axi_awid             (i_npu_mst1_axi_awid) //   > alb_mss_fab
  , .npu_mst1_axi_awvalid          (i_npu_mst1_axi_awvalid) //   > alb_mss_fab
  , .npu_mst1_axi_awaddr           (i_npu_mst1_axi_awaddr) //   > alb_mss_fab
  , .npu_mst1_axi_awburst          (i_npu_mst1_axi_awburst) //   > alb_mss_fab
  , .npu_mst1_axi_awsize           (i_npu_mst1_axi_awsize) //   > alb_mss_fab
  , .npu_mst1_axi_awlock           (i_npu_mst1_axi_awlock) //   > alb_mss_fab
  , .npu_mst1_axi_awlen            (i_npu_mst1_axi_awlen) //   > alb_mss_fab
  , .npu_mst1_axi_awcache          (i_npu_mst1_axi_awcache) //   > alb_mss_fab
  , .npu_mst1_axi_awprot           (i_npu_mst1_axi_awprot) //   > alb_mss_fab
  , .npu_mst1_axi_wvalid           (i_npu_mst1_axi_wvalid) //   > alb_mss_fab
  , .npu_mst1_axi_wdata            (i_npu_mst1_axi_wdata) //   > alb_mss_fab
  , .npu_mst1_axi_wstrb            (i_npu_mst1_axi_wstrb) //   > alb_mss_fab
  , .npu_mst1_axi_wlast            (i_npu_mst1_axi_wlast) //   > alb_mss_fab
  , .npu_mst1_axi_bready           (i_npu_mst1_axi_bready) //   > alb_mss_fab
  , .npu_mst2_axi_arid             (i_npu_mst2_axi_arid) //   > alb_mss_fab
  , .npu_mst2_axi_arvalid          (i_npu_mst2_axi_arvalid) //   > alb_mss_fab
  , .npu_mst2_axi_araddr           (i_npu_mst2_axi_araddr) //   > alb_mss_fab
  , .npu_mst2_axi_arburst          (i_npu_mst2_axi_arburst) //   > alb_mss_fab
  , .npu_mst2_axi_arsize           (i_npu_mst2_axi_arsize) //   > alb_mss_fab
  , .npu_mst2_axi_arlock           (i_npu_mst2_axi_arlock) //   > alb_mss_fab
  , .npu_mst2_axi_arlen            (i_npu_mst2_axi_arlen) //   > alb_mss_fab
  , .npu_mst2_axi_arcache          (i_npu_mst2_axi_arcache) //   > alb_mss_fab
  , .npu_mst2_axi_arprot           (i_npu_mst2_axi_arprot) //   > alb_mss_fab
  , .npu_mst2_axi_rready           (i_npu_mst2_axi_rready) //   > alb_mss_fab
  , .npu_mst2_axi_awid             (i_npu_mst2_axi_awid) //   > alb_mss_fab
  , .npu_mst2_axi_awvalid          (i_npu_mst2_axi_awvalid) //   > alb_mss_fab
  , .npu_mst2_axi_awaddr           (i_npu_mst2_axi_awaddr) //   > alb_mss_fab
  , .npu_mst2_axi_awburst          (i_npu_mst2_axi_awburst) //   > alb_mss_fab
  , .npu_mst2_axi_awsize           (i_npu_mst2_axi_awsize) //   > alb_mss_fab
  , .npu_mst2_axi_awlock           (i_npu_mst2_axi_awlock) //   > alb_mss_fab
  , .npu_mst2_axi_awlen            (i_npu_mst2_axi_awlen) //   > alb_mss_fab
  , .npu_mst2_axi_awcache          (i_npu_mst2_axi_awcache) //   > alb_mss_fab
  , .npu_mst2_axi_awprot           (i_npu_mst2_axi_awprot) //   > alb_mss_fab
  , .npu_mst2_axi_wvalid           (i_npu_mst2_axi_wvalid) //   > alb_mss_fab
  , .npu_mst2_axi_wdata            (i_npu_mst2_axi_wdata) //   > alb_mss_fab
  , .npu_mst2_axi_wstrb            (i_npu_mst2_axi_wstrb) //   > alb_mss_fab
  , .npu_mst2_axi_wlast            (i_npu_mst2_axi_wlast) //   > alb_mss_fab
  , .npu_mst2_axi_bready           (i_npu_mst2_axi_bready) //   > alb_mss_fab
  , .npu_mst3_axi_arid             (i_npu_mst3_axi_arid) //   > alb_mss_fab
  , .npu_mst3_axi_arvalid          (i_npu_mst3_axi_arvalid) //   > alb_mss_fab
  , .npu_mst3_axi_araddr           (i_npu_mst3_axi_araddr) //   > alb_mss_fab
  , .npu_mst3_axi_arburst          (i_npu_mst3_axi_arburst) //   > alb_mss_fab
  , .npu_mst3_axi_arsize           (i_npu_mst3_axi_arsize) //   > alb_mss_fab
  , .npu_mst3_axi_arlock           (i_npu_mst3_axi_arlock) //   > alb_mss_fab
  , .npu_mst3_axi_arlen            (i_npu_mst3_axi_arlen) //   > alb_mss_fab
  , .npu_mst3_axi_arcache          (i_npu_mst3_axi_arcache) //   > alb_mss_fab
  , .npu_mst3_axi_arprot           (i_npu_mst3_axi_arprot) //   > alb_mss_fab
  , .npu_mst3_axi_rready           (i_npu_mst3_axi_rready) //   > alb_mss_fab
  , .npu_mst3_axi_awid             (i_npu_mst3_axi_awid) //   > alb_mss_fab
  , .npu_mst3_axi_awvalid          (i_npu_mst3_axi_awvalid) //   > alb_mss_fab
  , .npu_mst3_axi_awaddr           (i_npu_mst3_axi_awaddr) //   > alb_mss_fab
  , .npu_mst3_axi_awburst          (i_npu_mst3_axi_awburst) //   > alb_mss_fab
  , .npu_mst3_axi_awsize           (i_npu_mst3_axi_awsize) //   > alb_mss_fab
  , .npu_mst3_axi_awlock           (i_npu_mst3_axi_awlock) //   > alb_mss_fab
  , .npu_mst3_axi_awlen            (i_npu_mst3_axi_awlen) //   > alb_mss_fab
  , .npu_mst3_axi_awcache          (i_npu_mst3_axi_awcache) //   > alb_mss_fab
  , .npu_mst3_axi_awprot           (i_npu_mst3_axi_awprot) //   > alb_mss_fab
  , .npu_mst3_axi_wvalid           (i_npu_mst3_axi_wvalid) //   > alb_mss_fab
  , .npu_mst3_axi_wdata            (i_npu_mst3_axi_wdata) //   > alb_mss_fab
  , .npu_mst3_axi_wstrb            (i_npu_mst3_axi_wstrb) //   > alb_mss_fab
  , .npu_mst3_axi_wlast            (i_npu_mst3_axi_wlast) //   > alb_mss_fab
  , .npu_mst3_axi_bready           (i_npu_mst3_axi_bready) //   > alb_mss_fab
  , .npu_mst4_axi_arid             (i_npu_mst4_axi_arid) //   > alb_mss_fab
  , .npu_mst4_axi_arvalid          (i_npu_mst4_axi_arvalid) //   > alb_mss_fab
  , .npu_mst4_axi_araddr           (i_npu_mst4_axi_araddr) //   > alb_mss_fab
  , .npu_mst4_axi_arburst          (i_npu_mst4_axi_arburst) //   > alb_mss_fab
  , .npu_mst4_axi_arsize           (i_npu_mst4_axi_arsize) //   > alb_mss_fab
  , .npu_mst4_axi_arlock           (i_npu_mst4_axi_arlock) //   > alb_mss_fab
  , .npu_mst4_axi_arlen            (i_npu_mst4_axi_arlen) //   > alb_mss_fab
  , .npu_mst4_axi_arcache          (i_npu_mst4_axi_arcache) //   > alb_mss_fab
  , .npu_mst4_axi_arprot           (i_npu_mst4_axi_arprot) //   > alb_mss_fab
  , .npu_mst4_axi_rready           (i_npu_mst4_axi_rready) //   > alb_mss_fab
  , .npu_mst4_axi_awid             (i_npu_mst4_axi_awid) //   > alb_mss_fab
  , .npu_mst4_axi_awvalid          (i_npu_mst4_axi_awvalid) //   > alb_mss_fab
  , .npu_mst4_axi_awaddr           (i_npu_mst4_axi_awaddr) //   > alb_mss_fab
  , .npu_mst4_axi_awburst          (i_npu_mst4_axi_awburst) //   > alb_mss_fab
  , .npu_mst4_axi_awsize           (i_npu_mst4_axi_awsize) //   > alb_mss_fab
  , .npu_mst4_axi_awlock           (i_npu_mst4_axi_awlock) //   > alb_mss_fab
  , .npu_mst4_axi_awlen            (i_npu_mst4_axi_awlen) //   > alb_mss_fab
  , .npu_mst4_axi_awcache          (i_npu_mst4_axi_awcache) //   > alb_mss_fab
  , .npu_mst4_axi_awprot           (i_npu_mst4_axi_awprot) //   > alb_mss_fab
  , .npu_mst4_axi_wvalid           (i_npu_mst4_axi_wvalid) //   > alb_mss_fab
  , .npu_mst4_axi_wdata            (i_npu_mst4_axi_wdata) //   > alb_mss_fab
  , .npu_mst4_axi_wstrb            (i_npu_mst4_axi_wstrb) //   > alb_mss_fab
  , .npu_mst4_axi_wlast            (i_npu_mst4_axi_wlast) //   > alb_mss_fab
  , .npu_mst4_axi_bready           (i_npu_mst4_axi_bready) //   > alb_mss_fab
  , .npu_dmi0_axi_arready          (i_npu_dmi0_axi_arready) //   > alb_mss_fab
  , .npu_dmi0_axi_rid              (i_npu_dmi0_axi_rid) //   > alb_mss_fab
  , .npu_dmi0_axi_rvalid           (i_npu_dmi0_axi_rvalid) //   > alb_mss_fab
  , .npu_dmi0_axi_rdata            (i_npu_dmi0_axi_rdata) //   > alb_mss_fab
  , .npu_dmi0_axi_rresp            (i_npu_dmi0_axi_rresp) //   > alb_mss_fab
  , .npu_dmi0_axi_rlast            (i_npu_dmi0_axi_rlast) //   > alb_mss_fab
  , .npu_dmi0_axi_awready          (i_npu_dmi0_axi_awready) //   > alb_mss_fab
  , .npu_dmi0_axi_wready           (i_npu_dmi0_axi_wready) //   > alb_mss_fab
  , .npu_dmi0_axi_bid              (i_npu_dmi0_axi_bid) //   > alb_mss_fab
  , .npu_dmi0_axi_bvalid           (i_npu_dmi0_axi_bvalid) //   > alb_mss_fab
  , .npu_dmi0_axi_bresp            (i_npu_dmi0_axi_bresp) //   > alb_mss_fab
  , .npu_cfg_axi_arready           (i_npu_cfg_axi_arready) //   > alb_mss_fab
  , .npu_cfg_axi_rid               (i_npu_cfg_axi_rid) //   > alb_mss_fab
  , .npu_cfg_axi_rvalid            (i_npu_cfg_axi_rvalid) //   > alb_mss_fab
  , .npu_cfg_axi_rdata             (i_npu_cfg_axi_rdata) //   > alb_mss_fab
  , .npu_cfg_axi_rresp             (i_npu_cfg_axi_rresp) //   > alb_mss_fab
  , .npu_cfg_axi_rlast             (i_npu_cfg_axi_rlast) //   > alb_mss_fab
  , .npu_cfg_axi_awready           (i_npu_cfg_axi_awready) //   > alb_mss_fab
  , .npu_cfg_axi_wready            (i_npu_cfg_axi_wready) //   > alb_mss_fab
  , .npu_cfg_axi_bid               (i_npu_cfg_axi_bid) //   > alb_mss_fab
  , .npu_cfg_axi_bvalid            (i_npu_cfg_axi_bvalid) //   > alb_mss_fab
  , .npu_cfg_axi_bresp             (i_npu_cfg_axi_bresp) //   > alb_mss_fab
  , .arcsync_axi_arready           (i_arcsync_axi_arready) //   > alb_mss_fab
  , .arcsync_axi_rid               (i_arcsync_axi_rid) //   > alb_mss_fab
  , .arcsync_axi_rvalid            (i_arcsync_axi_rvalid) //   > alb_mss_fab
  , .arcsync_axi_rdata             (i_arcsync_axi_rdata) //   > alb_mss_fab
  , .arcsync_axi_rresp             (i_arcsync_axi_rresp) //   > alb_mss_fab
  , .arcsync_axi_rlast             (i_arcsync_axi_rlast) //   > alb_mss_fab
  , .arcsync_axi_awready           (i_arcsync_axi_awready) //   > alb_mss_fab
  , .arcsync_axi_wready            (i_arcsync_axi_wready) //   > alb_mss_fab
  , .arcsync_axi_bid               (i_arcsync_axi_bid) //   > alb_mss_fab
  , .arcsync_axi_bvalid            (i_arcsync_axi_bvalid) //   > alb_mss_fab
  , .arcsync_axi_bresp             (i_arcsync_axi_bresp) //   > alb_mss_fab
  , .npu_mst1_axi_arsid            (npu_mst1_axi_arsid) //   > core_sys_stub
  , .npu_mst1_axi_arssid           (npu_mst1_axi_arssid) //   > core_sys_stub
  , .npu_mst1_axi_awsid            (npu_mst1_axi_awsid) //   > core_sys_stub
  , .npu_mst1_axi_awssid           (npu_mst1_axi_awssid) //   > core_sys_stub
  , .npu_mst2_axi_arsid            (npu_mst2_axi_arsid) //   > core_sys_stub
  , .npu_mst2_axi_arssid           (npu_mst2_axi_arssid) //   > core_sys_stub
  , .npu_mst2_axi_awsid            (npu_mst2_axi_awsid) //   > core_sys_stub
  , .npu_mst2_axi_awssid           (npu_mst2_axi_awssid) //   > core_sys_stub
  , .npu_mst3_axi_arsid            (npu_mst3_axi_arsid) //   > core_sys_stub
  , .npu_mst3_axi_arssid           (npu_mst3_axi_arssid) //   > core_sys_stub
  , .npu_mst3_axi_awsid            (npu_mst3_axi_awsid) //   > core_sys_stub
  , .npu_mst3_axi_awssid           (npu_mst3_axi_awssid) //   > core_sys_stub
  , .npu_mst4_axi_arsid            (npu_mst4_axi_arsid) //   > core_sys_stub
  , .npu_mst4_axi_arssid           (npu_mst4_axi_arssid) //   > core_sys_stub
  , .npu_mst4_axi_awsid            (npu_mst4_axi_awsid) //   > core_sys_stub
  , .npu_mst4_axi_awssid           (npu_mst4_axi_awssid) //   > core_sys_stub
  , .sl0_ecc_sbe                   (sl0_ecc_sbe)   //   > core_sys_stub
  , .sl0_ecc_dbe                   (sl0_ecc_dbe)   //   > core_sys_stub
  , .sl1_ecc_sbe                   (sl1_ecc_sbe)   //   > core_sys_stub
  , .sl1_ecc_dbe                   (sl1_ecc_dbe)   //   > core_sys_stub
  , .sl2_ecc_sbe                   (sl2_ecc_sbe)   //   > core_sys_stub
  , .sl2_ecc_dbe                   (sl2_ecc_dbe)   //   > core_sys_stub
  , .sl3_ecc_sbe                   (sl3_ecc_sbe)   //   > core_sys_stub
  , .sl3_ecc_dbe                   (sl3_ecc_dbe)   //   > core_sys_stub
  , .sl4_ecc_sbe                   (sl4_ecc_sbe)   //   > core_sys_stub
  , .sl4_ecc_dbe                   (sl4_ecc_dbe)   //   > core_sys_stub
  , .sl5_ecc_sbe                   (sl5_ecc_sbe)   //   > core_sys_stub
  , .sl5_ecc_dbe                   (sl5_ecc_dbe)   //   > core_sys_stub
  , .sl6_ecc_sbe                   (sl6_ecc_sbe)   //   > core_sys_stub
  , .sl6_ecc_dbe                   (sl6_ecc_dbe)   //   > core_sys_stub
  , .sl7_ecc_sbe                   (sl7_ecc_sbe)   //   > core_sys_stub
  , .sl7_ecc_dbe                   (sl7_ecc_dbe)   //   > core_sys_stub
  , .sl8_ecc_sbe                   (sl8_ecc_sbe)   //   > core_sys_stub
  , .sl8_ecc_dbe                   (sl8_ecc_dbe)   //   > core_sys_stub
  , .sl9_ecc_sbe                   (sl9_ecc_sbe)   //   > core_sys_stub
  , .sl9_ecc_dbe                   (sl9_ecc_dbe)   //   > core_sys_stub
  , .sl10_ecc_sbe                  (sl10_ecc_sbe)  //   > core_sys_stub
  , .sl10_ecc_dbe                  (sl10_ecc_dbe)  //   > core_sys_stub
  , .sl11_ecc_sbe                  (sl11_ecc_sbe)  //   > core_sys_stub
  , .sl11_ecc_dbe                  (sl11_ecc_dbe)  //   > core_sys_stub
  , .sl12_ecc_sbe                  (sl12_ecc_sbe)  //   > core_sys_stub
  , .sl12_ecc_dbe                  (sl12_ecc_dbe)  //   > core_sys_stub
  , .sl13_ecc_sbe                  (sl13_ecc_sbe)  //   > core_sys_stub
  , .sl13_ecc_dbe                  (sl13_ecc_dbe)  //   > core_sys_stub
  , .sl14_ecc_sbe                  (sl14_ecc_sbe)  //   > core_sys_stub
  , .sl14_ecc_dbe                  (sl14_ecc_dbe)  //   > core_sys_stub
  , .sl15_ecc_sbe                  (sl15_ecc_sbe)  //   > core_sys_stub
  , .sl15_ecc_dbe                  (sl15_ecc_dbe)  //   > core_sys_stub
  , .grp0_scm_dbank_sbe            (grp0_scm_dbank_sbe) //   > core_sys_stub
  , .grp0_scm_dbank_dbe            (grp0_scm_dbank_dbe) //   > core_sys_stub
  , .grp1_scm_dbank_sbe            (grp1_scm_dbank_sbe) //   > core_sys_stub
  , .grp1_scm_dbank_dbe            (grp1_scm_dbank_dbe) //   > core_sys_stub
  , .grp2_scm_dbank_sbe            (grp2_scm_dbank_sbe) //   > core_sys_stub
  , .grp2_scm_dbank_dbe            (grp2_scm_dbank_dbe) //   > core_sys_stub
  , .grp3_scm_dbank_sbe            (grp3_scm_dbank_sbe) //   > core_sys_stub
  , .grp3_scm_dbank_dbe            (grp3_scm_dbank_dbe) //   > core_sys_stub
  , .nl2arc0_ecc_sbe               (nl2arc0_ecc_sbe) //   > core_sys_stub
  , .nl2arc0_ecc_dbe               (nl2arc0_ecc_dbe) //   > core_sys_stub
  , .nl2arc1_ecc_sbe               (nl2arc1_ecc_sbe) //   > core_sys_stub
  , .nl2arc1_ecc_dbe               (nl2arc1_ecc_dbe) //   > core_sys_stub
  , .nl2arc0_evt_vm_irq            (nl2arc0_evt_vm_irq) //   > outside-of-hierarchy
  , .nl2arc1_evt_vm_irq            (nl2arc1_evt_vm_irq) //   > outside-of-hierarchy
  , .atdata                        (atdata)        //   > outside-of-hierarchy
  , .atbytes                       (atbytes)       //   > outside-of-hierarchy
  , .atid                          (atid)          //   > outside-of-hierarchy
  , .atvalid                       (atvalid)       //   > outside-of-hierarchy
  , .afready                       (afready)       //   > outside-of-hierarchy
  , .swe_atdata                    (swe_atdata)    //   > outside-of-hierarchy
  , .swe_atbytes                   (swe_atbytes)   //   > outside-of-hierarchy
  , .swe_atid                      (swe_atid)      //   > outside-of-hierarchy
  , .swe_atvalid                   (swe_atvalid)   //   > outside-of-hierarchy
  , .swe_afready                   (swe_afready)   //   > outside-of-hierarchy
  , .cti_rtt_filters               (cti_rtt_filters) //   > outside-of-hierarchy
  , .arct0_preadydbg               (arct0_preadydbg) //   > outside-of-hierarchy
  , .arct0_prdatadbg               (arct0_prdatadbg) //   > outside-of-hierarchy
  , .arct0_pslverrdbg              (arct0_pslverrdbg) //   > outside-of-hierarchy
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

// Instantiation of module arcsync_top_stub
arcsync_top_stub iarcsync_top_stub(
    .nl2arc_isolate_n       (i_nl2arc_isolate_n)   // <   core_archipelago.arcsync_top
  , .nl2arc_isolate         (i_nl2arc_isolate)     // <   core_archipelago.arcsync_top
  , .nl2arc_pd_mem          (i_nl2arc_pd_mem)      // <   core_archipelago.arcsync_top
  , .nl2arc_pd_logic        (i_nl2arc_pd_logic)    // <   core_archipelago.arcsync_top
  , .nl2arc_pd_logic1       (i_nl2arc_pd_logic1)   // <   core_archipelago.arcsync_top
  , .nl2arc_pd_logic2       (i_nl2arc_pd_logic2)   // <   core_archipelago.arcsync_top
  , .grp0_isolate_n         (i_grp0_isolate_n)     // <   core_archipelago.arcsync_top
  , .grp0_isolate           (i_grp0_isolate)       // <   core_archipelago.arcsync_top
  , .grp0_pd_mem            (i_grp0_pd_mem)        // <   core_archipelago.arcsync_top
  , .grp0_pd_logic          (i_grp0_pd_logic)      // <   core_archipelago.arcsync_top
  , .grp0_pd_logic1         (i_grp0_pd_logic1)     // <   core_archipelago.arcsync_top
  , .grp0_pd_logic2         (i_grp0_pd_logic2)     // <   core_archipelago.arcsync_top
  , .grp1_isolate_n         (i_grp1_isolate_n)     // <   core_archipelago.arcsync_top
  , .grp1_isolate           (i_grp1_isolate)       // <   core_archipelago.arcsync_top
  , .grp1_pd_mem            (i_grp1_pd_mem)        // <   core_archipelago.arcsync_top
  , .grp1_pd_logic          (i_grp1_pd_logic)      // <   core_archipelago.arcsync_top
  , .grp1_pd_logic1         (i_grp1_pd_logic1)     // <   core_archipelago.arcsync_top
  , .grp1_pd_logic2         (i_grp1_pd_logic2)     // <   core_archipelago.arcsync_top
  , .grp2_isolate_n         (i_grp2_isolate_n)     // <   core_archipelago.arcsync_top
  , .grp2_isolate           (i_grp2_isolate)       // <   core_archipelago.arcsync_top
  , .grp2_pd_mem            (i_grp2_pd_mem)        // <   core_archipelago.arcsync_top
  , .grp2_pd_logic          (i_grp2_pd_logic)      // <   core_archipelago.arcsync_top
  , .grp2_pd_logic1         (i_grp2_pd_logic1)     // <   core_archipelago.arcsync_top
  , .grp2_pd_logic2         (i_grp2_pd_logic2)     // <   core_archipelago.arcsync_top
  , .grp3_isolate_n         (i_grp3_isolate_n)     // <   core_archipelago.arcsync_top
  , .grp3_isolate           (i_grp3_isolate)       // <   core_archipelago.arcsync_top
  , .grp3_pd_mem            (i_grp3_pd_mem)        // <   core_archipelago.arcsync_top
  , .grp3_pd_logic          (i_grp3_pd_logic)      // <   core_archipelago.arcsync_top
  , .grp3_pd_logic1         (i_grp3_pd_logic1)     // <   core_archipelago.arcsync_top
  , .grp3_pd_logic2         (i_grp3_pd_logic2)     // <   core_archipelago.arcsync_top
  , .sl0nl1arc_isolate_n    (i_sl0nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl0nl1arc_isolate      (i_sl0nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl0nl1arc_pd_mem       (i_sl0nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl0nl1arc_pd_logic     (i_sl0nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl0nl1arc_pd_logic1    (i_sl0nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl0nl1arc_pd_logic2    (i_sl0nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl1nl1arc_isolate_n    (i_sl1nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl1nl1arc_isolate      (i_sl1nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl1nl1arc_pd_mem       (i_sl1nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl1nl1arc_pd_logic     (i_sl1nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl1nl1arc_pd_logic1    (i_sl1nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl1nl1arc_pd_logic2    (i_sl1nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl2nl1arc_isolate_n    (i_sl2nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl2nl1arc_isolate      (i_sl2nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl2nl1arc_pd_mem       (i_sl2nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl2nl1arc_pd_logic     (i_sl2nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl2nl1arc_pd_logic1    (i_sl2nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl2nl1arc_pd_logic2    (i_sl2nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl3nl1arc_isolate_n    (i_sl3nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl3nl1arc_isolate      (i_sl3nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl3nl1arc_pd_mem       (i_sl3nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl3nl1arc_pd_logic     (i_sl3nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl3nl1arc_pd_logic1    (i_sl3nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl3nl1arc_pd_logic2    (i_sl3nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl4nl1arc_isolate_n    (i_sl4nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl4nl1arc_isolate      (i_sl4nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl4nl1arc_pd_mem       (i_sl4nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl4nl1arc_pd_logic     (i_sl4nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl4nl1arc_pd_logic1    (i_sl4nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl4nl1arc_pd_logic2    (i_sl4nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl5nl1arc_isolate_n    (i_sl5nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl5nl1arc_isolate      (i_sl5nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl5nl1arc_pd_mem       (i_sl5nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl5nl1arc_pd_logic     (i_sl5nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl5nl1arc_pd_logic1    (i_sl5nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl5nl1arc_pd_logic2    (i_sl5nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl6nl1arc_isolate_n    (i_sl6nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl6nl1arc_isolate      (i_sl6nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl6nl1arc_pd_mem       (i_sl6nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl6nl1arc_pd_logic     (i_sl6nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl6nl1arc_pd_logic1    (i_sl6nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl6nl1arc_pd_logic2    (i_sl6nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl7nl1arc_isolate_n    (i_sl7nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl7nl1arc_isolate      (i_sl7nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl7nl1arc_pd_mem       (i_sl7nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl7nl1arc_pd_logic     (i_sl7nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl7nl1arc_pd_logic1    (i_sl7nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl7nl1arc_pd_logic2    (i_sl7nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl8nl1arc_isolate_n    (i_sl8nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl8nl1arc_isolate      (i_sl8nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl8nl1arc_pd_mem       (i_sl8nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl8nl1arc_pd_logic     (i_sl8nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl8nl1arc_pd_logic1    (i_sl8nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl8nl1arc_pd_logic2    (i_sl8nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl9nl1arc_isolate_n    (i_sl9nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl9nl1arc_isolate      (i_sl9nl1arc_isolate)  // <   core_archipelago.arcsync_top
  , .sl9nl1arc_pd_mem       (i_sl9nl1arc_pd_mem)   // <   core_archipelago.arcsync_top
  , .sl9nl1arc_pd_logic     (i_sl9nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl9nl1arc_pd_logic1    (i_sl9nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl9nl1arc_pd_logic2    (i_sl9nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl10nl1arc_isolate_n   (i_sl10nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl10nl1arc_isolate     (i_sl10nl1arc_isolate) // <   core_archipelago.arcsync_top
  , .sl10nl1arc_pd_mem      (i_sl10nl1arc_pd_mem)  // <   core_archipelago.arcsync_top
  , .sl10nl1arc_pd_logic    (i_sl10nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl10nl1arc_pd_logic1   (i_sl10nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl10nl1arc_pd_logic2   (i_sl10nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl11nl1arc_isolate_n   (i_sl11nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl11nl1arc_isolate     (i_sl11nl1arc_isolate) // <   core_archipelago.arcsync_top
  , .sl11nl1arc_pd_mem      (i_sl11nl1arc_pd_mem)  // <   core_archipelago.arcsync_top
  , .sl11nl1arc_pd_logic    (i_sl11nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl11nl1arc_pd_logic1   (i_sl11nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl11nl1arc_pd_logic2   (i_sl11nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl12nl1arc_isolate_n   (i_sl12nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl12nl1arc_isolate     (i_sl12nl1arc_isolate) // <   core_archipelago.arcsync_top
  , .sl12nl1arc_pd_mem      (i_sl12nl1arc_pd_mem)  // <   core_archipelago.arcsync_top
  , .sl12nl1arc_pd_logic    (i_sl12nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl12nl1arc_pd_logic1   (i_sl12nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl12nl1arc_pd_logic2   (i_sl12nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl13nl1arc_isolate_n   (i_sl13nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl13nl1arc_isolate     (i_sl13nl1arc_isolate) // <   core_archipelago.arcsync_top
  , .sl13nl1arc_pd_mem      (i_sl13nl1arc_pd_mem)  // <   core_archipelago.arcsync_top
  , .sl13nl1arc_pd_logic    (i_sl13nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl13nl1arc_pd_logic1   (i_sl13nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl13nl1arc_pd_logic2   (i_sl13nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl14nl1arc_isolate_n   (i_sl14nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl14nl1arc_isolate     (i_sl14nl1arc_isolate) // <   core_archipelago.arcsync_top
  , .sl14nl1arc_pd_mem      (i_sl14nl1arc_pd_mem)  // <   core_archipelago.arcsync_top
  , .sl14nl1arc_pd_logic    (i_sl14nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl14nl1arc_pd_logic1   (i_sl14nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl14nl1arc_pd_logic2   (i_sl14nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .sl15nl1arc_isolate_n   (i_sl15nl1arc_isolate_n) // <   core_archipelago.arcsync_top
  , .sl15nl1arc_isolate     (i_sl15nl1arc_isolate) // <   core_archipelago.arcsync_top
  , .sl15nl1arc_pd_mem      (i_sl15nl1arc_pd_mem)  // <   core_archipelago.arcsync_top
  , .sl15nl1arc_pd_logic    (i_sl15nl1arc_pd_logic) // <   core_archipelago.arcsync_top
  , .sl15nl1arc_pd_logic1   (i_sl15nl1arc_pd_logic1) // <   core_archipelago.arcsync_top
  , .sl15nl1arc_pd_logic2   (i_sl15nl1arc_pd_logic2) // <   core_archipelago.arcsync_top
  , .v0csm_addr_base        (i_v0csm_addr_base)    // <   core_archipelago.arcsync_top
  , .v0periph_addr_base     (i_v0periph_addr_base) // <   core_archipelago.arcsync_top
  , .v0clusternum           (i_v0clusternum)       // <   core_archipelago.arcsync_top
  , .v0c0arcnum             (i_v0c0arcnum)         // <   core_archipelago.arcsync_top
  , .v0c0intvbase           (i_v0c0intvbase)       // <   core_archipelago.arcsync_top
  , .v0c0rst_a              (i_v0c0rst_a)          // <   core_archipelago.arcsync_top
  , .v0c0clk_en             (i_v0c0clk_en)         // <   core_archipelago.arcsync_top
  , .v0c0arc_halt_req       (i_v0c0arc_halt_req)   // <   core_archipelago.arcsync_top
  , .v0c0ext_arc_halt_ack   (i_v0c0ext_arc_halt_ack) // <   core_archipelago.arcsync_top
  , .v0c0arc_run_req        (i_v0c0arc_run_req)    // <   core_archipelago.arcsync_top
  , .v0c0ext_arc_run_ack    (i_v0c0ext_arc_run_ack) // <   core_archipelago.arcsync_top
  , .v0c0arc_irq0_a         (i_v0c0arc_irq0_a)     // <   core_archipelago.arcsync_top
  , .v0c0arc_irq1_a         (i_v0c0arc_irq1_a)     // <   core_archipelago.arcsync_top
  , .v0c0arc_event0_a       (i_v0c0arc_event0_a)   // <   core_archipelago.arcsync_top
  , .v0c0arc_event1_a       (i_v0c0arc_event1_a)   // <   core_archipelago.arcsync_top
  , .v0c1arcnum             (i_v0c1arcnum)         // <   core_archipelago.arcsync_top
  , .v0c1intvbase           (i_v0c1intvbase)       // <   core_archipelago.arcsync_top
  , .v0c1rst_a              (i_v0c1rst_a)          // <   core_archipelago.arcsync_top
  , .v0c1clk_en             (i_v0c1clk_en)         // <   core_archipelago.arcsync_top
  , .v0c1arc_halt_req       (i_v0c1arc_halt_req)   // <   core_archipelago.arcsync_top
  , .v0c1ext_arc_halt_ack   (i_v0c1ext_arc_halt_ack) // <   core_archipelago.arcsync_top
  , .v0c1arc_run_req        (i_v0c1arc_run_req)    // <   core_archipelago.arcsync_top
  , .v0c1ext_arc_run_ack    (i_v0c1ext_arc_run_ack) // <   core_archipelago.arcsync_top
  , .v0c1arc_irq0_a         (i_v0c1arc_irq0_a)     // <   core_archipelago.arcsync_top
  , .v0c1arc_irq1_a         (i_v0c1arc_irq1_a)     // <   core_archipelago.arcsync_top
  , .v0c1arc_event0_a       (i_v0c1arc_event0_a)   // <   core_archipelago.arcsync_top
  , .v0c1arc_event1_a       (i_v0c1arc_event1_a)   // <   core_archipelago.arcsync_top
  , .v0c2arcnum             (i_v0c2arcnum)         // <   core_archipelago.arcsync_top
  , .v0c2intvbase           (i_v0c2intvbase)       // <   core_archipelago.arcsync_top
  , .v0c2rst_a              (i_v0c2rst_a)          // <   core_archipelago.arcsync_top
  , .v0c2clk_en             (i_v0c2clk_en)         // <   core_archipelago.arcsync_top
  , .v0c2arc_halt_req       (i_v0c2arc_halt_req)   // <   core_archipelago.arcsync_top
  , .v0c2ext_arc_halt_ack   (i_v0c2ext_arc_halt_ack) // <   core_archipelago.arcsync_top
  , .v0c2arc_run_req        (i_v0c2arc_run_req)    // <   core_archipelago.arcsync_top
  , .v0c2ext_arc_run_ack    (i_v0c2ext_arc_run_ack) // <   core_archipelago.arcsync_top
  , .v0c2arc_irq0_a         (i_v0c2arc_irq0_a)     // <   core_archipelago.arcsync_top
  , .v0c2arc_irq1_a         (i_v0c2arc_irq1_a)     // <   core_archipelago.arcsync_top
  , .v0c2arc_event0_a       (i_v0c2arc_event0_a)   // <   core_archipelago.arcsync_top
  , .v0c2arc_event1_a       (i_v0c2arc_event1_a)   // <   core_archipelago.arcsync_top
  , .v0c3arcnum             (i_v0c3arcnum)         // <   core_archipelago.arcsync_top
  , .v0c3intvbase           (i_v0c3intvbase)       // <   core_archipelago.arcsync_top
  , .v0c3rst_a              (i_v0c3rst_a)          // <   core_archipelago.arcsync_top
  , .v0c3clk_en             (i_v0c3clk_en)         // <   core_archipelago.arcsync_top
  , .v0c3arc_halt_req       (i_v0c3arc_halt_req)   // <   core_archipelago.arcsync_top
  , .v0c3ext_arc_halt_ack   (i_v0c3ext_arc_halt_ack) // <   core_archipelago.arcsync_top
  , .v0c3arc_run_req        (i_v0c3arc_run_req)    // <   core_archipelago.arcsync_top
  , .v0c3ext_arc_run_ack    (i_v0c3ext_arc_run_ack) // <   core_archipelago.arcsync_top
  , .v0c3arc_irq0_a         (i_v0c3arc_irq0_a)     // <   core_archipelago.arcsync_top
  , .v0c3arc_irq1_a         (i_v0c3arc_irq1_a)     // <   core_archipelago.arcsync_top
  , .v0c3arc_event0_a       (i_v0c3arc_event0_a)   // <   core_archipelago.arcsync_top
  , .v0c3arc_event1_a       (i_v0c3arc_event1_a)   // <   core_archipelago.arcsync_top
  , .vpx_v0_vm0_irq0_a      (i_vpx_v0_vm0_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm0_irq_ac_a    (i_vpx_v0_vm0_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm0_evt0_a      (i_vpx_v0_vm0_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm0_evt_ac_a    (i_vpx_v0_vm0_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm1_irq0_a      (i_vpx_v0_vm1_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm1_irq_ac_a    (i_vpx_v0_vm1_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm1_evt0_a      (i_vpx_v0_vm1_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm1_evt_ac_a    (i_vpx_v0_vm1_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm2_irq0_a      (i_vpx_v0_vm2_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm2_irq_ac_a    (i_vpx_v0_vm2_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm2_evt0_a      (i_vpx_v0_vm2_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm2_evt_ac_a    (i_vpx_v0_vm2_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm3_irq0_a      (i_vpx_v0_vm3_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm3_irq_ac_a    (i_vpx_v0_vm3_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm3_evt0_a      (i_vpx_v0_vm3_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm3_evt_ac_a    (i_vpx_v0_vm3_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm4_irq0_a      (i_vpx_v0_vm4_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm4_irq_ac_a    (i_vpx_v0_vm4_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm4_evt0_a      (i_vpx_v0_vm4_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm4_evt_ac_a    (i_vpx_v0_vm4_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm5_irq0_a      (i_vpx_v0_vm5_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm5_irq_ac_a    (i_vpx_v0_vm5_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm5_evt0_a      (i_vpx_v0_vm5_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm5_evt_ac_a    (i_vpx_v0_vm5_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm6_irq0_a      (i_vpx_v0_vm6_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm6_irq_ac_a    (i_vpx_v0_vm6_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm6_evt0_a      (i_vpx_v0_vm6_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm6_evt_ac_a    (i_vpx_v0_vm6_evt_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm7_irq0_a      (i_vpx_v0_vm7_irq0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm7_irq_ac_a    (i_vpx_v0_vm7_irq_ac_a) // <   core_archipelago.arcsync_top
  , .vpx_v0_vm7_evt0_a      (i_vpx_v0_vm7_evt0_a)  // <   core_archipelago.arcsync_top
  , .vpx_v0_vm7_evt_ac_a    (i_vpx_v0_vm7_evt_ac_a) // <   core_archipelago.arcsync_top
  , .v0c0_isolate_n         (i_v0c0_isolate_n)     // <   core_archipelago.arcsync_top
  , .v0c0_isolate           (i_v0c0_isolate)       // <   core_archipelago.arcsync_top
  , .v0c0_pd_mem            (i_v0c0_pd_mem)        // <   core_archipelago.arcsync_top
  , .v0c0_pd_logic          (i_v0c0_pd_logic)      // <   core_archipelago.arcsync_top
  , .v0c0_pd_logic1         (i_v0c0_pd_logic1)     // <   core_archipelago.arcsync_top
  , .v0c0_pd_logic2         (i_v0c0_pd_logic2)     // <   core_archipelago.arcsync_top
  , .v0c1_isolate_n         (i_v0c1_isolate_n)     // <   core_archipelago.arcsync_top
  , .v0c1_isolate           (i_v0c1_isolate)       // <   core_archipelago.arcsync_top
  , .v0c1_pd_mem            (i_v0c1_pd_mem)        // <   core_archipelago.arcsync_top
  , .v0c1_pd_logic          (i_v0c1_pd_logic)      // <   core_archipelago.arcsync_top
  , .v0c1_pd_logic1         (i_v0c1_pd_logic1)     // <   core_archipelago.arcsync_top
  , .v0c1_pd_logic2         (i_v0c1_pd_logic2)     // <   core_archipelago.arcsync_top
  , .v0c2_isolate_n         (i_v0c2_isolate_n)     // <   core_archipelago.arcsync_top
  , .v0c2_isolate           (i_v0c2_isolate)       // <   core_archipelago.arcsync_top
  , .v0c2_pd_mem            (i_v0c2_pd_mem)        // <   core_archipelago.arcsync_top
  , .v0c2_pd_logic          (i_v0c2_pd_logic)      // <   core_archipelago.arcsync_top
  , .v0c2_pd_logic1         (i_v0c2_pd_logic1)     // <   core_archipelago.arcsync_top
  , .v0c2_pd_logic2         (i_v0c2_pd_logic2)     // <   core_archipelago.arcsync_top
  , .v0c3_isolate_n         (i_v0c3_isolate_n)     // <   core_archipelago.arcsync_top
  , .v0c3_isolate           (i_v0c3_isolate)       // <   core_archipelago.arcsync_top
  , .v0c3_pd_mem            (i_v0c3_pd_mem)        // <   core_archipelago.arcsync_top
  , .v0c3_pd_logic          (i_v0c3_pd_logic)      // <   core_archipelago.arcsync_top
  , .v0c3_pd_logic1         (i_v0c3_pd_logic1)     // <   core_archipelago.arcsync_top
  , .v0c3_pd_logic2         (i_v0c3_pd_logic2)     // <   core_archipelago.arcsync_top
  , .arcsync_clk            (arcsync_clk)          // <   outside-of-hierarchy
  , .arcsync_rst_a          (arcsync_rst_a)        // <   outside-of-hierarchy
  , .v0c0arc_halt_ack_a     (i_v0c0arc_halt_ack_a) //   > core_archipelago
  , .v0c0ext_arc_halt_req_a (i_v0c0ext_arc_halt_req_a) //   > core_archipelago
  , .v0c0arc_run_ack_a      (i_v0c0arc_run_ack_a)  //   > core_archipelago
  , .v0c0ext_arc_run_req_a  (i_v0c0ext_arc_run_req_a) //   > core_archipelago
  , .v0c0sys_sleep_r        (i_v0c0sys_sleep_r)    //   > core_archipelago
  , .v0c0sys_sleep_mode_r   (i_v0c0sys_sleep_mode_r) //   > core_archipelago
  , .v0c0sys_halt_r         (i_v0c0sys_halt_r)     //   > core_archipelago
  , .v0c0sys_tf_halt_r      (i_v0c0sys_tf_halt_r)  //   > core_archipelago
  , .v0c0pmode              (i_v0c0pmode)          //   > core_archipelago
  , .v0c1arc_halt_ack_a     (i_v0c1arc_halt_ack_a) //   > core_archipelago
  , .v0c1ext_arc_halt_req_a (i_v0c1ext_arc_halt_req_a) //   > core_archipelago
  , .v0c1arc_run_ack_a      (i_v0c1arc_run_ack_a)  //   > core_archipelago
  , .v0c1ext_arc_run_req_a  (i_v0c1ext_arc_run_req_a) //   > core_archipelago
  , .v0c1sys_sleep_r        (i_v0c1sys_sleep_r)    //   > core_archipelago
  , .v0c1sys_sleep_mode_r   (i_v0c1sys_sleep_mode_r) //   > core_archipelago
  , .v0c1sys_halt_r         (i_v0c1sys_halt_r)     //   > core_archipelago
  , .v0c1sys_tf_halt_r      (i_v0c1sys_tf_halt_r)  //   > core_archipelago
  , .v0c1pmode              (i_v0c1pmode)          //   > core_archipelago
  , .v0c2arc_halt_ack_a     (i_v0c2arc_halt_ack_a) //   > core_archipelago
  , .v0c2ext_arc_halt_req_a (i_v0c2ext_arc_halt_req_a) //   > core_archipelago
  , .v0c2arc_run_ack_a      (i_v0c2arc_run_ack_a)  //   > core_archipelago
  , .v0c2ext_arc_run_req_a  (i_v0c2ext_arc_run_req_a) //   > core_archipelago
  , .v0c2sys_sleep_r        (i_v0c2sys_sleep_r)    //   > core_archipelago
  , .v0c2sys_sleep_mode_r   (i_v0c2sys_sleep_mode_r) //   > core_archipelago
  , .v0c2sys_halt_r         (i_v0c2sys_halt_r)     //   > core_archipelago
  , .v0c2sys_tf_halt_r      (i_v0c2sys_tf_halt_r)  //   > core_archipelago
  , .v0c2pmode              (i_v0c2pmode)          //   > core_archipelago
  , .v0c3arc_halt_ack_a     (i_v0c3arc_halt_ack_a) //   > core_archipelago
  , .v0c3ext_arc_halt_req_a (i_v0c3ext_arc_halt_req_a) //   > core_archipelago
  , .v0c3arc_run_ack_a      (i_v0c3arc_run_ack_a)  //   > core_archipelago
  , .v0c3ext_arc_run_req_a  (i_v0c3ext_arc_run_req_a) //   > core_archipelago
  , .v0c3sys_sleep_r        (i_v0c3sys_sleep_r)    //   > core_archipelago
  , .v0c3sys_sleep_mode_r   (i_v0c3sys_sleep_mode_r) //   > core_archipelago
  , .v0c3sys_halt_r         (i_v0c3sys_halt_r)     //   > core_archipelago
  , .v0c3sys_tf_halt_r      (i_v0c3sys_tf_halt_r)  //   > core_archipelago
  , .v0c3pmode              (i_v0c3pmode)          //   > core_archipelago
  );

// Instantiation of module alb_mss_fab
alb_mss_fab ialb_mss_fab(
    .npu_mst0_axi_arid      (i_npu_mst0_axi_arid)  // <   core_archipelago.npu_top
  , .npu_mst0_axi_arvalid   (i_npu_mst0_axi_arvalid) // <   core_archipelago.npu_top
  , .npu_mst0_axi_araddr    (i_npu_mst0_axi_araddr) // <   core_archipelago.npu_top
  , .npu_mst0_axi_arburst   (i_npu_mst0_axi_arburst) // <   core_archipelago.npu_top
  , .npu_mst0_axi_arsize    (i_npu_mst0_axi_arsize) // <   core_archipelago.npu_top
  , .npu_mst0_axi_arlock    (i_npu_mst0_axi_arlock) // <   core_archipelago.npu_top
  , .npu_mst0_axi_arlen     (i_npu_mst0_axi_arlen) // <   core_archipelago.npu_top
  , .npu_mst0_axi_arcache   (i_npu_mst0_axi_arcache) // <   core_archipelago.npu_top
  , .npu_mst0_axi_arprot    (i_npu_mst0_axi_arprot) // <   core_archipelago.npu_top
  , .npu_mst0_axi_rready    (i_npu_mst0_axi_rready) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awid      (i_npu_mst0_axi_awid)  // <   core_archipelago.npu_top
  , .npu_mst0_axi_awvalid   (i_npu_mst0_axi_awvalid) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awaddr    (i_npu_mst0_axi_awaddr) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awburst   (i_npu_mst0_axi_awburst) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awsize    (i_npu_mst0_axi_awsize) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awlock    (i_npu_mst0_axi_awlock) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awlen     (i_npu_mst0_axi_awlen) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awcache   (i_npu_mst0_axi_awcache) // <   core_archipelago.npu_top
  , .npu_mst0_axi_awprot    (i_npu_mst0_axi_awprot) // <   core_archipelago.npu_top
  , .npu_mst0_axi_wvalid    (i_npu_mst0_axi_wvalid) // <   core_archipelago.npu_top
  , .npu_mst0_axi_wdata     (i_npu_mst0_axi_wdata) // <   core_archipelago.npu_top
  , .npu_mst0_axi_wstrb     (i_npu_mst0_axi_wstrb) // <   core_archipelago.npu_top
  , .npu_mst0_axi_wlast     (i_npu_mst0_axi_wlast) // <   core_archipelago.npu_top
  , .npu_mst0_axi_bready    (i_npu_mst0_axi_bready) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arid      (i_npu_mst1_axi_arid)  // <   core_archipelago.npu_top
  , .npu_mst1_axi_arvalid   (i_npu_mst1_axi_arvalid) // <   core_archipelago.npu_top
  , .npu_mst1_axi_araddr    (i_npu_mst1_axi_araddr) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arburst   (i_npu_mst1_axi_arburst) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arsize    (i_npu_mst1_axi_arsize) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arlock    (i_npu_mst1_axi_arlock) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arlen     (i_npu_mst1_axi_arlen) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arcache   (i_npu_mst1_axi_arcache) // <   core_archipelago.npu_top
  , .npu_mst1_axi_arprot    (i_npu_mst1_axi_arprot) // <   core_archipelago.npu_top
  , .npu_mst1_axi_rready    (i_npu_mst1_axi_rready) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awid      (i_npu_mst1_axi_awid)  // <   core_archipelago.npu_top
  , .npu_mst1_axi_awvalid   (i_npu_mst1_axi_awvalid) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awaddr    (i_npu_mst1_axi_awaddr) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awburst   (i_npu_mst1_axi_awburst) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awsize    (i_npu_mst1_axi_awsize) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awlock    (i_npu_mst1_axi_awlock) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awlen     (i_npu_mst1_axi_awlen) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awcache   (i_npu_mst1_axi_awcache) // <   core_archipelago.npu_top
  , .npu_mst1_axi_awprot    (i_npu_mst1_axi_awprot) // <   core_archipelago.npu_top
  , .npu_mst1_axi_wvalid    (i_npu_mst1_axi_wvalid) // <   core_archipelago.npu_top
  , .npu_mst1_axi_wdata     (i_npu_mst1_axi_wdata) // <   core_archipelago.npu_top
  , .npu_mst1_axi_wstrb     (i_npu_mst1_axi_wstrb) // <   core_archipelago.npu_top
  , .npu_mst1_axi_wlast     (i_npu_mst1_axi_wlast) // <   core_archipelago.npu_top
  , .npu_mst1_axi_bready    (i_npu_mst1_axi_bready) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arid      (i_npu_mst2_axi_arid)  // <   core_archipelago.npu_top
  , .npu_mst2_axi_arvalid   (i_npu_mst2_axi_arvalid) // <   core_archipelago.npu_top
  , .npu_mst2_axi_araddr    (i_npu_mst2_axi_araddr) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arburst   (i_npu_mst2_axi_arburst) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arsize    (i_npu_mst2_axi_arsize) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arlock    (i_npu_mst2_axi_arlock) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arlen     (i_npu_mst2_axi_arlen) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arcache   (i_npu_mst2_axi_arcache) // <   core_archipelago.npu_top
  , .npu_mst2_axi_arprot    (i_npu_mst2_axi_arprot) // <   core_archipelago.npu_top
  , .npu_mst2_axi_rready    (i_npu_mst2_axi_rready) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awid      (i_npu_mst2_axi_awid)  // <   core_archipelago.npu_top
  , .npu_mst2_axi_awvalid   (i_npu_mst2_axi_awvalid) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awaddr    (i_npu_mst2_axi_awaddr) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awburst   (i_npu_mst2_axi_awburst) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awsize    (i_npu_mst2_axi_awsize) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awlock    (i_npu_mst2_axi_awlock) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awlen     (i_npu_mst2_axi_awlen) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awcache   (i_npu_mst2_axi_awcache) // <   core_archipelago.npu_top
  , .npu_mst2_axi_awprot    (i_npu_mst2_axi_awprot) // <   core_archipelago.npu_top
  , .npu_mst2_axi_wvalid    (i_npu_mst2_axi_wvalid) // <   core_archipelago.npu_top
  , .npu_mst2_axi_wdata     (i_npu_mst2_axi_wdata) // <   core_archipelago.npu_top
  , .npu_mst2_axi_wstrb     (i_npu_mst2_axi_wstrb) // <   core_archipelago.npu_top
  , .npu_mst2_axi_wlast     (i_npu_mst2_axi_wlast) // <   core_archipelago.npu_top
  , .npu_mst2_axi_bready    (i_npu_mst2_axi_bready) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arid      (i_npu_mst3_axi_arid)  // <   core_archipelago.npu_top
  , .npu_mst3_axi_arvalid   (i_npu_mst3_axi_arvalid) // <   core_archipelago.npu_top
  , .npu_mst3_axi_araddr    (i_npu_mst3_axi_araddr) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arburst   (i_npu_mst3_axi_arburst) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arsize    (i_npu_mst3_axi_arsize) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arlock    (i_npu_mst3_axi_arlock) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arlen     (i_npu_mst3_axi_arlen) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arcache   (i_npu_mst3_axi_arcache) // <   core_archipelago.npu_top
  , .npu_mst3_axi_arprot    (i_npu_mst3_axi_arprot) // <   core_archipelago.npu_top
  , .npu_mst3_axi_rready    (i_npu_mst3_axi_rready) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awid      (i_npu_mst3_axi_awid)  // <   core_archipelago.npu_top
  , .npu_mst3_axi_awvalid   (i_npu_mst3_axi_awvalid) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awaddr    (i_npu_mst3_axi_awaddr) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awburst   (i_npu_mst3_axi_awburst) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awsize    (i_npu_mst3_axi_awsize) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awlock    (i_npu_mst3_axi_awlock) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awlen     (i_npu_mst3_axi_awlen) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awcache   (i_npu_mst3_axi_awcache) // <   core_archipelago.npu_top
  , .npu_mst3_axi_awprot    (i_npu_mst3_axi_awprot) // <   core_archipelago.npu_top
  , .npu_mst3_axi_wvalid    (i_npu_mst3_axi_wvalid) // <   core_archipelago.npu_top
  , .npu_mst3_axi_wdata     (i_npu_mst3_axi_wdata) // <   core_archipelago.npu_top
  , .npu_mst3_axi_wstrb     (i_npu_mst3_axi_wstrb) // <   core_archipelago.npu_top
  , .npu_mst3_axi_wlast     (i_npu_mst3_axi_wlast) // <   core_archipelago.npu_top
  , .npu_mst3_axi_bready    (i_npu_mst3_axi_bready) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arid      (i_npu_mst4_axi_arid)  // <   core_archipelago.npu_top
  , .npu_mst4_axi_arvalid   (i_npu_mst4_axi_arvalid) // <   core_archipelago.npu_top
  , .npu_mst4_axi_araddr    (i_npu_mst4_axi_araddr) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arburst   (i_npu_mst4_axi_arburst) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arsize    (i_npu_mst4_axi_arsize) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arlock    (i_npu_mst4_axi_arlock) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arlen     (i_npu_mst4_axi_arlen) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arcache   (i_npu_mst4_axi_arcache) // <   core_archipelago.npu_top
  , .npu_mst4_axi_arprot    (i_npu_mst4_axi_arprot) // <   core_archipelago.npu_top
  , .npu_mst4_axi_rready    (i_npu_mst4_axi_rready) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awid      (i_npu_mst4_axi_awid)  // <   core_archipelago.npu_top
  , .npu_mst4_axi_awvalid   (i_npu_mst4_axi_awvalid) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awaddr    (i_npu_mst4_axi_awaddr) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awburst   (i_npu_mst4_axi_awburst) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awsize    (i_npu_mst4_axi_awsize) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awlock    (i_npu_mst4_axi_awlock) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awlen     (i_npu_mst4_axi_awlen) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awcache   (i_npu_mst4_axi_awcache) // <   core_archipelago.npu_top
  , .npu_mst4_axi_awprot    (i_npu_mst4_axi_awprot) // <   core_archipelago.npu_top
  , .npu_mst4_axi_wvalid    (i_npu_mst4_axi_wvalid) // <   core_archipelago.npu_top
  , .npu_mst4_axi_wdata     (i_npu_mst4_axi_wdata) // <   core_archipelago.npu_top
  , .npu_mst4_axi_wstrb     (i_npu_mst4_axi_wstrb) // <   core_archipelago.npu_top
  , .npu_mst4_axi_wlast     (i_npu_mst4_axi_wlast) // <   core_archipelago.npu_top
  , .npu_mst4_axi_bready    (i_npu_mst4_axi_bready) // <   core_archipelago.npu_top
  , .host_axi_arid          (host_axi_arid)        // <   core_sys_stub
  , .host_axi_arvalid       (host_axi_arvalid)     // <   core_sys_stub
  , .host_axi_araddr        (host_axi_araddr)      // <   core_sys_stub
  , .host_axi_arburst       (host_axi_arburst)     // <   core_sys_stub
  , .host_axi_arsize        (host_axi_arsize)      // <   core_sys_stub
  , .host_axi_arlock        (host_axi_arlock)      // <   core_sys_stub
  , .host_axi_arlen         (host_axi_arlen)       // <   core_sys_stub
  , .host_axi_arcache       (host_axi_arcache)     // <   core_sys_stub
  , .host_axi_arprot        (host_axi_arprot)      // <   core_sys_stub
  , .host_axi_rready        (host_axi_rready)      // <   core_sys_stub
  , .host_axi_awid          (host_axi_awid)        // <   core_sys_stub
  , .host_axi_awvalid       (host_axi_awvalid)     // <   core_sys_stub
  , .host_axi_awaddr        (host_axi_awaddr)      // <   core_sys_stub
  , .host_axi_awburst       (host_axi_awburst)     // <   core_sys_stub
  , .host_axi_awsize        (host_axi_awsize)      // <   core_sys_stub
  , .host_axi_awlock        (host_axi_awlock)      // <   core_sys_stub
  , .host_axi_awlen         (host_axi_awlen)       // <   core_sys_stub
  , .host_axi_awcache       (host_axi_awcache)     // <   core_sys_stub
  , .host_axi_awprot        (host_axi_awprot)      // <   core_sys_stub
  , .host_axi_wvalid        (host_axi_wvalid)      // <   core_sys_stub
  , .host_axi_wdata         (host_axi_wdata)       // <   core_sys_stub
  , .host_axi_wstrb         (host_axi_wstrb)       // <   core_sys_stub
  , .host_axi_wlast         (host_axi_wlast)       // <   core_sys_stub
  , .host_axi_bready        (host_axi_bready)      // <   core_sys_stub
  , .bri4tb_arid            (bri4tb_arid)          // <   outside-of-hierarchy
  , .bri4tb_arvalid         (bri4tb_arvalid)       // <   outside-of-hierarchy
  , .bri4tb_araddr          (bri4tb_araddr)        // <   outside-of-hierarchy
  , .bri4tb_arburst         (bri4tb_arburst)       // <   outside-of-hierarchy
  , .bri4tb_arsize          (bri4tb_arsize)        // <   outside-of-hierarchy
  , .bri4tb_arlen           (bri4tb_arlen)         // <   outside-of-hierarchy
  , .bri4tb_arcache         (bri4tb_arcache)       // <   outside-of-hierarchy
  , .bri4tb_arprot          (bri4tb_arprot)        // <   outside-of-hierarchy
  , .bri4tb_rready          (bri4tb_rready)        // <   outside-of-hierarchy
  , .bri4tb_awid            (bri4tb_awid)          // <   outside-of-hierarchy
  , .bri4tb_awvalid         (bri4tb_awvalid)       // <   outside-of-hierarchy
  , .bri4tb_awaddr          (bri4tb_awaddr)        // <   outside-of-hierarchy
  , .bri4tb_awburst         (bri4tb_awburst)       // <   outside-of-hierarchy
  , .bri4tb_awsize          (bri4tb_awsize)        // <   outside-of-hierarchy
  , .bri4tb_awlen           (bri4tb_awlen)         // <   outside-of-hierarchy
  , .bri4tb_awcache         (bri4tb_awcache)       // <   outside-of-hierarchy
  , .bri4tb_awprot          (bri4tb_awprot)        // <   outside-of-hierarchy
  , .bri4tb_wid             (bri4tb_wid)           // <   outside-of-hierarchy
  , .bri4tb_wvalid          (bri4tb_wvalid)        // <   outside-of-hierarchy
  , .bri4tb_wdata           (bri4tb_wdata)         // <   outside-of-hierarchy
  , .bri4tb_wstrb           (bri4tb_wstrb)         // <   outside-of-hierarchy
  , .bri4tb_wlast           (bri4tb_wlast)         // <   outside-of-hierarchy
  , .bri4tb_bready          (bri4tb_bready)        // <   outside-of-hierarchy
  , .npu_dmi0_axi_arready   (i_npu_dmi0_axi_arready) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_rid       (i_npu_dmi0_axi_rid)   // <   core_archipelago.npu_top
  , .npu_dmi0_axi_rvalid    (i_npu_dmi0_axi_rvalid) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_rdata     (i_npu_dmi0_axi_rdata) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_rresp     (i_npu_dmi0_axi_rresp) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_rlast     (i_npu_dmi0_axi_rlast) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_awready   (i_npu_dmi0_axi_awready) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_wready    (i_npu_dmi0_axi_wready) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_bid       (i_npu_dmi0_axi_bid)   // <   core_archipelago.npu_top
  , .npu_dmi0_axi_bvalid    (i_npu_dmi0_axi_bvalid) // <   core_archipelago.npu_top
  , .npu_dmi0_axi_bresp     (i_npu_dmi0_axi_bresp) // <   core_archipelago.npu_top
  , .npu_cfg_axi_arready    (i_npu_cfg_axi_arready) // <   core_archipelago.npu_top
  , .npu_cfg_axi_rid        (i_npu_cfg_axi_rid)    // <   core_archipelago.npu_top
  , .npu_cfg_axi_rvalid     (i_npu_cfg_axi_rvalid) // <   core_archipelago.npu_top
  , .npu_cfg_axi_rdata      (i_npu_cfg_axi_rdata)  // <   core_archipelago.npu_top
  , .npu_cfg_axi_rresp      (i_npu_cfg_axi_rresp)  // <   core_archipelago.npu_top
  , .npu_cfg_axi_rlast      (i_npu_cfg_axi_rlast)  // <   core_archipelago.npu_top
  , .npu_cfg_axi_awready    (i_npu_cfg_axi_awready) // <   core_archipelago.npu_top
  , .npu_cfg_axi_wready     (i_npu_cfg_axi_wready) // <   core_archipelago.npu_top
  , .npu_cfg_axi_bid        (i_npu_cfg_axi_bid)    // <   core_archipelago.npu_top
  , .npu_cfg_axi_bvalid     (i_npu_cfg_axi_bvalid) // <   core_archipelago.npu_top
  , .npu_cfg_axi_bresp      (i_npu_cfg_axi_bresp)  // <   core_archipelago.npu_top
  , .arcsync_axi_arready    (i_arcsync_axi_arready) // <   core_archipelago.arcsync_top
  , .arcsync_axi_rid        (i_arcsync_axi_rid)    // <   core_archipelago.arcsync_top
  , .arcsync_axi_rvalid     (i_arcsync_axi_rvalid) // <   core_archipelago.arcsync_top
  , .arcsync_axi_rdata      (i_arcsync_axi_rdata)  // <   core_archipelago.arcsync_top
  , .arcsync_axi_rresp      (i_arcsync_axi_rresp)  // <   core_archipelago.arcsync_top
  , .arcsync_axi_rlast      (i_arcsync_axi_rlast)  // <   core_archipelago.arcsync_top
  , .arcsync_axi_awready    (i_arcsync_axi_awready) // <   core_archipelago.arcsync_top
  , .arcsync_axi_wready     (i_arcsync_axi_wready) // <   core_archipelago.arcsync_top
  , .arcsync_axi_bid        (i_arcsync_axi_bid)    // <   core_archipelago.arcsync_top
  , .arcsync_axi_bvalid     (i_arcsync_axi_bvalid) // <   core_archipelago.arcsync_top
  , .arcsync_axi_bresp      (i_arcsync_axi_bresp)  // <   core_archipelago.arcsync_top
  , .mss_mem_cmd_accept     (i_mss_mem_cmd_accept) // <   alb_mss_mem
  , .mss_mem_rd_valid       (i_mss_mem_rd_valid)   // <   alb_mss_mem
  , .mss_mem_rd_excl_ok     (i_mss_mem_rd_excl_ok) // <   alb_mss_mem
  , .mss_mem_rd_data        (i_mss_mem_rd_data)    // <   alb_mss_mem
  , .mss_mem_err_rd         (i_mss_mem_err_rd)     // <   alb_mss_mem
  , .mss_mem_rd_last        (i_mss_mem_rd_last)    // <   alb_mss_mem
  , .mss_mem_wr_accept      (i_mss_mem_wr_accept)  // <   alb_mss_mem
  , .mss_mem_wr_done        (i_mss_mem_wr_done)    // <   alb_mss_mem
  , .mss_mem_wr_excl_done   (i_mss_mem_wr_excl_done) // <   alb_mss_mem
  , .mss_mem_err_wr         (i_mss_mem_err_wr)     // <   alb_mss_mem
  , .clk                    (clk)                  // <   outside-of-hierarchy
  , .mss_clk                (mss_clk)              // <   outside-of-hierarchy
  , .mss_fab_mst0_clk_en    (mss_fab_mst0_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_mst1_clk_en    (mss_fab_mst1_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_mst2_clk_en    (mss_fab_mst2_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_mst3_clk_en    (mss_fab_mst3_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_mst4_clk_en    (mss_fab_mst4_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_mst5_clk_en    (mss_fab_mst5_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_mst6_clk_en    (mss_fab_mst6_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_slv0_clk_en    (mss_fab_slv0_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_slv1_clk_en    (mss_fab_slv1_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_slv2_clk_en    (mss_fab_slv2_clk_en)  // <   outside-of-hierarchy
  , .mss_fab_slv3_clk_en    (mss_fab_slv3_clk_en)  // <   outside-of-hierarchy
  , .rst_b                  (rst_b)                // <   outside-of-hierarchy
  , .npu_mst0_axi_arready   (i_npu_mst0_axi_arready) //   > core_archipelago
  , .npu_mst0_axi_rvalid    (i_npu_mst0_axi_rvalid) //   > core_archipelago
  , .npu_mst0_axi_rid       (i_npu_mst0_axi_rid)   //   > core_archipelago
  , .npu_mst0_axi_rdata     (i_npu_mst0_axi_rdata) //   > core_archipelago
  , .npu_mst0_axi_rresp     (i_npu_mst0_axi_rresp) //   > core_archipelago
  , .npu_mst0_axi_rlast     (i_npu_mst0_axi_rlast) //   > core_archipelago
  , .npu_mst0_axi_awready   (i_npu_mst0_axi_awready) //   > core_archipelago
  , .npu_mst0_axi_wready    (i_npu_mst0_axi_wready) //   > core_archipelago
  , .npu_mst0_axi_bvalid    (i_npu_mst0_axi_bvalid) //   > core_archipelago
  , .npu_mst0_axi_bid       (i_npu_mst0_axi_bid)   //   > core_archipelago
  , .npu_mst0_axi_bresp     (i_npu_mst0_axi_bresp) //   > core_archipelago
  , .npu_mst1_axi_arready   (i_npu_mst1_axi_arready) //   > core_archipelago
  , .npu_mst1_axi_rvalid    (i_npu_mst1_axi_rvalid) //   > core_archipelago
  , .npu_mst1_axi_rid       (i_npu_mst1_axi_rid)   //   > core_archipelago
  , .npu_mst1_axi_rdata     (i_npu_mst1_axi_rdata) //   > core_archipelago
  , .npu_mst1_axi_rresp     (i_npu_mst1_axi_rresp) //   > core_archipelago
  , .npu_mst1_axi_rlast     (i_npu_mst1_axi_rlast) //   > core_archipelago
  , .npu_mst1_axi_awready   (i_npu_mst1_axi_awready) //   > core_archipelago
  , .npu_mst1_axi_wready    (i_npu_mst1_axi_wready) //   > core_archipelago
  , .npu_mst1_axi_bvalid    (i_npu_mst1_axi_bvalid) //   > core_archipelago
  , .npu_mst1_axi_bid       (i_npu_mst1_axi_bid)   //   > core_archipelago
  , .npu_mst1_axi_bresp     (i_npu_mst1_axi_bresp) //   > core_archipelago
  , .npu_mst2_axi_arready   (i_npu_mst2_axi_arready) //   > core_archipelago
  , .npu_mst2_axi_rvalid    (i_npu_mst2_axi_rvalid) //   > core_archipelago
  , .npu_mst2_axi_rid       (i_npu_mst2_axi_rid)   //   > core_archipelago
  , .npu_mst2_axi_rdata     (i_npu_mst2_axi_rdata) //   > core_archipelago
  , .npu_mst2_axi_rresp     (i_npu_mst2_axi_rresp) //   > core_archipelago
  , .npu_mst2_axi_rlast     (i_npu_mst2_axi_rlast) //   > core_archipelago
  , .npu_mst2_axi_awready   (i_npu_mst2_axi_awready) //   > core_archipelago
  , .npu_mst2_axi_wready    (i_npu_mst2_axi_wready) //   > core_archipelago
  , .npu_mst2_axi_bvalid    (i_npu_mst2_axi_bvalid) //   > core_archipelago
  , .npu_mst2_axi_bid       (i_npu_mst2_axi_bid)   //   > core_archipelago
  , .npu_mst2_axi_bresp     (i_npu_mst2_axi_bresp) //   > core_archipelago
  , .npu_mst3_axi_arready   (i_npu_mst3_axi_arready) //   > core_archipelago
  , .npu_mst3_axi_rvalid    (i_npu_mst3_axi_rvalid) //   > core_archipelago
  , .npu_mst3_axi_rid       (i_npu_mst3_axi_rid)   //   > core_archipelago
  , .npu_mst3_axi_rdata     (i_npu_mst3_axi_rdata) //   > core_archipelago
  , .npu_mst3_axi_rresp     (i_npu_mst3_axi_rresp) //   > core_archipelago
  , .npu_mst3_axi_rlast     (i_npu_mst3_axi_rlast) //   > core_archipelago
  , .npu_mst3_axi_awready   (i_npu_mst3_axi_awready) //   > core_archipelago
  , .npu_mst3_axi_wready    (i_npu_mst3_axi_wready) //   > core_archipelago
  , .npu_mst3_axi_bvalid    (i_npu_mst3_axi_bvalid) //   > core_archipelago
  , .npu_mst3_axi_bid       (i_npu_mst3_axi_bid)   //   > core_archipelago
  , .npu_mst3_axi_bresp     (i_npu_mst3_axi_bresp) //   > core_archipelago
  , .npu_mst4_axi_arready   (i_npu_mst4_axi_arready) //   > core_archipelago
  , .npu_mst4_axi_rvalid    (i_npu_mst4_axi_rvalid) //   > core_archipelago
  , .npu_mst4_axi_rid       (i_npu_mst4_axi_rid)   //   > core_archipelago
  , .npu_mst4_axi_rdata     (i_npu_mst4_axi_rdata) //   > core_archipelago
  , .npu_mst4_axi_rresp     (i_npu_mst4_axi_rresp) //   > core_archipelago
  , .npu_mst4_axi_rlast     (i_npu_mst4_axi_rlast) //   > core_archipelago
  , .npu_mst4_axi_awready   (i_npu_mst4_axi_awready) //   > core_archipelago
  , .npu_mst4_axi_wready    (i_npu_mst4_axi_wready) //   > core_archipelago
  , .npu_mst4_axi_bvalid    (i_npu_mst4_axi_bvalid) //   > core_archipelago
  , .npu_mst4_axi_bid       (i_npu_mst4_axi_bid)   //   > core_archipelago
  , .npu_mst4_axi_bresp     (i_npu_mst4_axi_bresp) //   > core_archipelago
  , .npu_dmi0_axi_arvalid   (i_npu_dmi0_axi_arvalid) //   > core_archipelago
  , .npu_dmi0_axi_arid      (i_npu_dmi0_axi_arid)  //   > core_archipelago
  , .npu_dmi0_axi_araddr    (i_npu_dmi0_axi_araddr) //   > core_archipelago
  , .npu_dmi0_axi_arcache   (i_npu_dmi0_axi_arcache) //   > core_archipelago
  , .npu_dmi0_axi_arprot    (i_npu_dmi0_axi_arprot) //   > core_archipelago
  , .npu_dmi0_axi_arlock    (i_npu_dmi0_axi_arlock) //   > core_archipelago
  , .npu_dmi0_axi_arburst   (i_npu_dmi0_axi_arburst) //   > core_archipelago
  , .npu_dmi0_axi_arlen     (i_npu_dmi0_axi_arlen) //   > core_archipelago
  , .npu_dmi0_axi_arsize    (i_npu_dmi0_axi_arsize) //   > core_archipelago
  , .npu_dmi0_axi_rready    (i_npu_dmi0_axi_rready) //   > core_archipelago
  , .npu_dmi0_axi_awvalid   (i_npu_dmi0_axi_awvalid) //   > core_archipelago
  , .npu_dmi0_axi_awid      (i_npu_dmi0_axi_awid)  //   > core_archipelago
  , .npu_dmi0_axi_awaddr    (i_npu_dmi0_axi_awaddr) //   > core_archipelago
  , .npu_dmi0_axi_awcache   (i_npu_dmi0_axi_awcache) //   > core_archipelago
  , .npu_dmi0_axi_awprot    (i_npu_dmi0_axi_awprot) //   > core_archipelago
  , .npu_dmi0_axi_awlock    (i_npu_dmi0_axi_awlock) //   > core_archipelago
  , .npu_dmi0_axi_awburst   (i_npu_dmi0_axi_awburst) //   > core_archipelago
  , .npu_dmi0_axi_awlen     (i_npu_dmi0_axi_awlen) //   > core_archipelago
  , .npu_dmi0_axi_awsize    (i_npu_dmi0_axi_awsize) //   > core_archipelago
  , .npu_dmi0_axi_wvalid    (i_npu_dmi0_axi_wvalid) //   > core_archipelago
  , .npu_dmi0_axi_wdata     (i_npu_dmi0_axi_wdata) //   > core_archipelago
  , .npu_dmi0_axi_wstrb     (i_npu_dmi0_axi_wstrb) //   > core_archipelago
  , .npu_dmi0_axi_wlast     (i_npu_dmi0_axi_wlast) //   > core_archipelago
  , .npu_dmi0_axi_bready    (i_npu_dmi0_axi_bready) //   > core_archipelago
  , .npu_cfg_axi_arvalid    (i_npu_cfg_axi_arvalid) //   > core_archipelago
  , .npu_cfg_axi_arid       (i_npu_cfg_axi_arid)   //   > core_archipelago
  , .npu_cfg_axi_araddr     (i_npu_cfg_axi_araddr) //   > core_archipelago
  , .npu_cfg_axi_arcache    (i_npu_cfg_axi_arcache) //   > core_archipelago
  , .npu_cfg_axi_arprot     (i_npu_cfg_axi_arprot) //   > core_archipelago
  , .npu_cfg_axi_arlock     (i_npu_cfg_axi_arlock) //   > core_archipelago
  , .npu_cfg_axi_arburst    (i_npu_cfg_axi_arburst) //   > core_archipelago
  , .npu_cfg_axi_arlen      (i_npu_cfg_axi_arlen)  //   > core_archipelago
  , .npu_cfg_axi_arsize     (i_npu_cfg_axi_arsize) //   > core_archipelago
  , .npu_cfg_axi_rready     (i_npu_cfg_axi_rready) //   > core_archipelago
  , .npu_cfg_axi_awvalid    (i_npu_cfg_axi_awvalid) //   > core_archipelago
  , .npu_cfg_axi_awid       (i_npu_cfg_axi_awid)   //   > core_archipelago
  , .npu_cfg_axi_awaddr     (i_npu_cfg_axi_awaddr) //   > core_archipelago
  , .npu_cfg_axi_awcache    (i_npu_cfg_axi_awcache) //   > core_archipelago
  , .npu_cfg_axi_awprot     (i_npu_cfg_axi_awprot) //   > core_archipelago
  , .npu_cfg_axi_awlock     (i_npu_cfg_axi_awlock) //   > core_archipelago
  , .npu_cfg_axi_awburst    (i_npu_cfg_axi_awburst) //   > core_archipelago
  , .npu_cfg_axi_awlen      (i_npu_cfg_axi_awlen)  //   > core_archipelago
  , .npu_cfg_axi_awsize     (i_npu_cfg_axi_awsize) //   > core_archipelago
  , .npu_cfg_axi_wvalid     (i_npu_cfg_axi_wvalid) //   > core_archipelago
  , .npu_cfg_axi_wdata      (i_npu_cfg_axi_wdata)  //   > core_archipelago
  , .npu_cfg_axi_wstrb      (i_npu_cfg_axi_wstrb)  //   > core_archipelago
  , .npu_cfg_axi_wlast      (i_npu_cfg_axi_wlast)  //   > core_archipelago
  , .npu_cfg_axi_bready     (i_npu_cfg_axi_bready) //   > core_archipelago
  , .arcsync_axi_arvalid    (i_arcsync_axi_arvalid) //   > core_archipelago
  , .arcsync_axi_arid       (i_arcsync_axi_arid)   //   > core_archipelago
  , .arcsync_axi_araddr     (i_arcsync_axi_araddr) //   > core_archipelago
  , .arcsync_axi_arcache    (i_arcsync_axi_arcache) //   > core_archipelago
  , .arcsync_axi_arprot     (i_arcsync_axi_arprot) //   > core_archipelago
  , .arcsync_axi_arlock     (i_arcsync_axi_arlock) //   > core_archipelago
  , .arcsync_axi_arburst    (i_arcsync_axi_arburst) //   > core_archipelago
  , .arcsync_axi_arlen      (i_arcsync_axi_arlen)  //   > core_archipelago
  , .arcsync_axi_arsize     (i_arcsync_axi_arsize) //   > core_archipelago
  , .arcsync_axi_rready     (i_arcsync_axi_rready) //   > core_archipelago
  , .arcsync_axi_awvalid    (i_arcsync_axi_awvalid) //   > core_archipelago
  , .arcsync_axi_awid       (i_arcsync_axi_awid)   //   > core_archipelago
  , .arcsync_axi_awaddr     (i_arcsync_axi_awaddr) //   > core_archipelago
  , .arcsync_axi_awcache    (i_arcsync_axi_awcache) //   > core_archipelago
  , .arcsync_axi_awprot     (i_arcsync_axi_awprot) //   > core_archipelago
  , .arcsync_axi_awlock     (i_arcsync_axi_awlock) //   > core_archipelago
  , .arcsync_axi_awburst    (i_arcsync_axi_awburst) //   > core_archipelago
  , .arcsync_axi_awlen      (i_arcsync_axi_awlen)  //   > core_archipelago
  , .arcsync_axi_awsize     (i_arcsync_axi_awsize) //   > core_archipelago
  , .arcsync_axi_wvalid     (i_arcsync_axi_wvalid) //   > core_archipelago
  , .arcsync_axi_wdata      (i_arcsync_axi_wdata)  //   > core_archipelago
  , .arcsync_axi_wstrb      (i_arcsync_axi_wstrb)  //   > core_archipelago
  , .arcsync_axi_wlast      (i_arcsync_axi_wlast)  //   > core_archipelago
  , .arcsync_axi_bready     (i_arcsync_axi_bready) //   > core_archipelago
  , .mss_mem_cmd_valid      (i_mss_mem_cmd_valid)  //   > alb_mss_mem
  , .mss_mem_cmd_read       (i_mss_mem_cmd_read)   //   > alb_mss_mem
  , .mss_mem_cmd_addr       (i_mss_mem_cmd_addr)   //   > alb_mss_mem
  , .mss_mem_cmd_wrap       (i_mss_mem_cmd_wrap)   //   > alb_mss_mem
  , .mss_mem_cmd_data_size  (i_mss_mem_cmd_data_size) //   > alb_mss_mem
  , .mss_mem_cmd_burst_size (i_mss_mem_cmd_burst_size) //   > alb_mss_mem
  , .mss_mem_cmd_lock       (i_mss_mem_cmd_lock)   //   > alb_mss_mem
  , .mss_mem_cmd_excl       (i_mss_mem_cmd_excl)   //   > alb_mss_mem
  , .mss_mem_cmd_prot       (i_mss_mem_cmd_prot)   //   > alb_mss_mem
  , .mss_mem_cmd_cache      (i_mss_mem_cmd_cache)  //   > alb_mss_mem
  , .mss_mem_cmd_id         (i_mss_mem_cmd_id)     //   > alb_mss_mem
  , .mss_mem_cmd_user       (i_mss_mem_cmd_user)   //   > alb_mss_mem
  , .mss_mem_cmd_region     (i_mss_mem_cmd_region) //   > alb_mss_mem
  , .mss_mem_rd_accept      (i_mss_mem_rd_accept)  //   > alb_mss_mem
  , .mss_mem_wr_valid       (i_mss_mem_wr_valid)   //   > alb_mss_mem
  , .mss_mem_wr_data        (i_mss_mem_wr_data)    //   > alb_mss_mem
  , .mss_mem_wr_mask        (i_mss_mem_wr_mask)    //   > alb_mss_mem
  , .mss_mem_wr_last        (i_mss_mem_wr_last)    //   > alb_mss_mem
  , .mss_mem_wr_resp_accept (i_mss_mem_wr_resp_accept) //   > alb_mss_mem
  , .host_axi_arready       (host_axi_arready)     //   > core_sys_stub
  , .host_axi_rvalid        (host_axi_rvalid)      //   > core_sys_stub
  , .host_axi_rid           (host_axi_rid)         //   > core_sys_stub
  , .host_axi_rdata         (host_axi_rdata)       //   > core_sys_stub
  , .host_axi_rresp         (host_axi_rresp)       //   > core_sys_stub
  , .host_axi_rlast         (host_axi_rlast)       //   > core_sys_stub
  , .host_axi_awready       (host_axi_awready)     //   > core_sys_stub
  , .host_axi_wready        (host_axi_wready)      //   > core_sys_stub
  , .host_axi_bvalid        (host_axi_bvalid)      //   > core_sys_stub
  , .host_axi_bid           (host_axi_bid)         //   > core_sys_stub
  , .host_axi_bresp         (host_axi_bresp)       //   > core_sys_stub
  , .bri4tb_arready         (bri4tb_arready)       //   > outside-of-hierarchy
  , .bri4tb_rid             (bri4tb_rid)           //   > outside-of-hierarchy
  , .bri4tb_rvalid          (bri4tb_rvalid)        //   > outside-of-hierarchy
  , .bri4tb_rdata           (bri4tb_rdata)         //   > outside-of-hierarchy
  , .bri4tb_rresp           (bri4tb_rresp)         //   > outside-of-hierarchy
  , .bri4tb_rlast           (bri4tb_rlast)         //   > outside-of-hierarchy
  , .bri4tb_awready         (bri4tb_awready)       //   > outside-of-hierarchy
  , .bri4tb_wready          (bri4tb_wready)        //   > outside-of-hierarchy
  , .bri4tb_bid             (bri4tb_bid)           //   > outside-of-hierarchy
  , .bri4tb_bvalid          (bri4tb_bvalid)        //   > outside-of-hierarchy
  , .bri4tb_bresp           (bri4tb_bresp)         //   > outside-of-hierarchy
  );

// Instantiation of module alb_mss_mem
alb_mss_mem ialb_mss_mem(
    .mss_clk                (mss_clk)              // <   outside-of-hierarchy
  , .rst_b                  (rst_b)                // <   outside-of-hierarchy
  , .mss_mem_cmd_valid      (i_mss_mem_cmd_valid)  // <   alb_mss_fab
  , .mss_mem_cmd_read       (i_mss_mem_cmd_read)   // <   alb_mss_fab
  , .mss_mem_cmd_addr       (i_mss_mem_cmd_addr)   // <   alb_mss_fab
  , .mss_mem_cmd_wrap       (i_mss_mem_cmd_wrap)   // <   alb_mss_fab
  , .mss_mem_cmd_data_size  (i_mss_mem_cmd_data_size) // <   alb_mss_fab
  , .mss_mem_cmd_burst_size (i_mss_mem_cmd_burst_size) // <   alb_mss_fab
  , .mss_mem_cmd_lock       (i_mss_mem_cmd_lock)   // <   alb_mss_fab
  , .mss_mem_cmd_excl       (i_mss_mem_cmd_excl)   // <   alb_mss_fab
  , .mss_mem_cmd_prot       (i_mss_mem_cmd_prot)   // <   alb_mss_fab
  , .mss_mem_cmd_cache      (i_mss_mem_cmd_cache)  // <   alb_mss_fab
  , .mss_mem_cmd_id         (i_mss_mem_cmd_id)     // <   alb_mss_fab
  , .mss_mem_cmd_user       (i_mss_mem_cmd_user)   // <   alb_mss_fab
  , .mss_mem_cmd_region     (i_mss_mem_cmd_region) // <   alb_mss_fab
  , .mss_mem_rd_accept      (i_mss_mem_rd_accept)  // <   alb_mss_fab
  , .mss_mem_wr_valid       (i_mss_mem_wr_valid)   // <   alb_mss_fab
  , .mss_mem_wr_data        (i_mss_mem_wr_data)    // <   alb_mss_fab
  , .mss_mem_wr_mask        (i_mss_mem_wr_mask)    // <   alb_mss_fab
  , .mss_mem_wr_last        (i_mss_mem_wr_last)    // <   alb_mss_fab
  , .mss_mem_wr_resp_accept (i_mss_mem_wr_resp_accept) // <   alb_mss_fab
  , .mss_mem_cmd_accept     (i_mss_mem_cmd_accept) //   > alb_mss_fab
  , .mss_mem_rd_valid       (i_mss_mem_rd_valid)   //   > alb_mss_fab
  , .mss_mem_rd_excl_ok     (i_mss_mem_rd_excl_ok) //   > alb_mss_fab
  , .mss_mem_rd_data        (i_mss_mem_rd_data)    //   > alb_mss_fab
  , .mss_mem_err_rd         (i_mss_mem_err_rd)     //   > alb_mss_fab
  , .mss_mem_rd_last        (i_mss_mem_rd_last)    //   > alb_mss_fab
  , .mss_mem_wr_accept      (i_mss_mem_wr_accept)  //   > alb_mss_fab
  , .mss_mem_wr_done        (i_mss_mem_wr_done)    //   > alb_mss_fab
  , .mss_mem_wr_excl_done   (i_mss_mem_wr_excl_done) //   > alb_mss_fab
  , .mss_mem_err_wr         (i_mss_mem_err_wr)     //   > alb_mss_fab
  , .mss_mem_dummy          (i_mss_mem_dummy)      //   > unconnected
  );
endmodule
