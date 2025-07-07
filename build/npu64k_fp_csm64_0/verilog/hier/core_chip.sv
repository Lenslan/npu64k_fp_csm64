// This file was automatically generated.
// Includes found in dependent files:
`include "npu_defines.v"
`include "arcsync_exported_defines.v"
`include "arcsync_defines.v"
`include "alb_mss_fab_defines.v"
`include "alb_mss_mem_defines.v"

module core_chip(
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
wire   [1-1:0] i_host_axi_arid;          // core_sys_stub > core_sys -- core_sys_stub.host_axi_arid [1-1:0]
wire   i_host_axi_arvalid;               // core_sys_stub > core_sys -- core_sys_stub.host_axi_arvalid
wire   [40-1:0] i_host_axi_araddr;       // core_sys_stub > core_sys -- core_sys_stub.host_axi_araddr [40-1:0]
wire   [1:0] i_host_axi_arburst;         // core_sys_stub > core_sys -- core_sys_stub.host_axi_arburst [1:0]
wire   [2:0] i_host_axi_arsize;          // core_sys_stub > core_sys -- core_sys_stub.host_axi_arsize [2:0]
wire   [1-1:0] i_host_axi_arlock;        // core_sys_stub > core_sys -- core_sys_stub.host_axi_arlock [0:0]
wire   [3:0] i_host_axi_arlen;           // core_sys_stub > core_sys -- core_sys_stub.host_axi_arlen [3:0]
wire   [3:0] i_host_axi_arcache;         // core_sys_stub > core_sys -- core_sys_stub.host_axi_arcache [3:0]
wire   [2:0] i_host_axi_arprot;          // core_sys_stub > core_sys -- core_sys_stub.host_axi_arprot [2:0]
wire   i_host_axi_rready;                // core_sys_stub > core_sys -- core_sys_stub.host_axi_rready
wire   [1-1:0] i_host_axi_awid;          // core_sys_stub > core_sys -- core_sys_stub.host_axi_awid [1-1:0]
wire   i_host_axi_awvalid;               // core_sys_stub > core_sys -- core_sys_stub.host_axi_awvalid
wire   [40-1:0] i_host_axi_awaddr;       // core_sys_stub > core_sys -- core_sys_stub.host_axi_awaddr [40-1:0]
wire   [1:0] i_host_axi_awburst;         // core_sys_stub > core_sys -- core_sys_stub.host_axi_awburst [1:0]
wire   [2:0] i_host_axi_awsize;          // core_sys_stub > core_sys -- core_sys_stub.host_axi_awsize [2:0]
wire   [1-1:0] i_host_axi_awlock;        // core_sys_stub > core_sys -- core_sys_stub.host_axi_awlock [0:0]
wire   [3:0] i_host_axi_awlen;           // core_sys_stub > core_sys -- core_sys_stub.host_axi_awlen [3:0]
wire   [3:0] i_host_axi_awcache;         // core_sys_stub > core_sys -- core_sys_stub.host_axi_awcache [3:0]
wire   [2:0] i_host_axi_awprot;          // core_sys_stub > core_sys -- core_sys_stub.host_axi_awprot [2:0]
wire   i_host_axi_wvalid;                // core_sys_stub > core_sys -- core_sys_stub.host_axi_wvalid
wire   [64-1:0] i_host_axi_wdata;        // core_sys_stub > core_sys -- core_sys_stub.host_axi_wdata [64-1:0]
wire   [64/8-1:0] i_host_axi_wstrb;      // core_sys_stub > core_sys -- core_sys_stub.host_axi_wstrb [64/8-1:0]
wire   i_host_axi_wlast;                 // core_sys_stub > core_sys -- core_sys_stub.host_axi_wlast
wire   i_host_axi_bready;                // core_sys_stub > core_sys -- core_sys_stub.host_axi_bready
wire   [31:0] i_npu_mst1_axi_arsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst1_axi_arsid [31:0]
wire   [31:0] i_npu_mst1_axi_arssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst1_axi_arssid [31:0]
wire   [31:0] i_npu_mst1_axi_awsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst1_axi_awsid [31:0]
wire   [31:0] i_npu_mst1_axi_awssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst1_axi_awssid [31:0]
wire   [31:0] i_npu_mst2_axi_arsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst2_axi_arsid [31:0]
wire   [31:0] i_npu_mst2_axi_arssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst2_axi_arssid [31:0]
wire   [31:0] i_npu_mst2_axi_awsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst2_axi_awsid [31:0]
wire   [31:0] i_npu_mst2_axi_awssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst2_axi_awssid [31:0]
wire   [31:0] i_npu_mst3_axi_arsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst3_axi_arsid [31:0]
wire   [31:0] i_npu_mst3_axi_arssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst3_axi_arssid [31:0]
wire   [31:0] i_npu_mst3_axi_awsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst3_axi_awsid [31:0]
wire   [31:0] i_npu_mst3_axi_awssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst3_axi_awssid [31:0]
wire   [31:0] i_npu_mst4_axi_arsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst4_axi_arsid [31:0]
wire   [31:0] i_npu_mst4_axi_arssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst4_axi_arssid [31:0]
wire   [31:0] i_npu_mst4_axi_awsid;      // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst4_axi_awsid [31:0]
wire   [31:0] i_npu_mst4_axi_awssid;     // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.npu_mst4_axi_awssid [31:0]
wire   i_sl0_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl0_ecc_sbe
wire   i_sl0_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl0_ecc_dbe
wire   i_sl1_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl1_ecc_sbe
wire   i_sl1_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl1_ecc_dbe
wire   i_sl2_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl2_ecc_sbe
wire   i_sl2_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl2_ecc_dbe
wire   i_sl3_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl3_ecc_sbe
wire   i_sl3_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl3_ecc_dbe
wire   i_sl4_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl4_ecc_sbe
wire   i_sl4_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl4_ecc_dbe
wire   i_sl5_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl5_ecc_sbe
wire   i_sl5_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl5_ecc_dbe
wire   i_sl6_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl6_ecc_sbe
wire   i_sl6_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl6_ecc_dbe
wire   i_sl7_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl7_ecc_sbe
wire   i_sl7_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl7_ecc_dbe
wire   i_sl8_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl8_ecc_sbe
wire   i_sl8_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl8_ecc_dbe
wire   i_sl9_ecc_sbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl9_ecc_sbe
wire   i_sl9_ecc_dbe;                    // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl9_ecc_dbe
wire   i_sl10_ecc_sbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl10_ecc_sbe
wire   i_sl10_ecc_dbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl10_ecc_dbe
wire   i_sl11_ecc_sbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl11_ecc_sbe
wire   i_sl11_ecc_dbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl11_ecc_dbe
wire   i_sl12_ecc_sbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl12_ecc_sbe
wire   i_sl12_ecc_dbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl12_ecc_dbe
wire   i_sl13_ecc_sbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl13_ecc_sbe
wire   i_sl13_ecc_dbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl13_ecc_dbe
wire   i_sl14_ecc_sbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl14_ecc_sbe
wire   i_sl14_ecc_dbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl14_ecc_dbe
wire   i_sl15_ecc_sbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl15_ecc_sbe
wire   i_sl15_ecc_dbe;                   // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.sl15_ecc_dbe
wire   i_grp0_scm_dbank_sbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp0_scm_dbank_sbe
wire   i_grp0_scm_dbank_dbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp0_scm_dbank_dbe
wire   i_grp1_scm_dbank_sbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp1_scm_dbank_sbe
wire   i_grp1_scm_dbank_dbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp1_scm_dbank_dbe
wire   i_grp2_scm_dbank_sbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp2_scm_dbank_sbe
wire   i_grp2_scm_dbank_dbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp2_scm_dbank_dbe
wire   i_grp3_scm_dbank_sbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp3_scm_dbank_sbe
wire   i_grp3_scm_dbank_dbe;             // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.grp3_scm_dbank_dbe
wire   i_nl2arc0_ecc_sbe;                // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.nl2arc0_ecc_sbe
wire   i_nl2arc0_ecc_dbe;                // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.nl2arc0_ecc_dbe
wire   i_nl2arc1_ecc_sbe;                // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.nl2arc1_ecc_sbe
wire   i_nl2arc1_ecc_dbe;                // core_sys > core_sys_stub -- core_sys.core_archipelago.npu_top.nl2arc1_ecc_dbe
wire   i_host_axi_arready;               // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_arready
wire   i_host_axi_rvalid;                // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_rvalid
wire   [0:0] i_host_axi_rid;             // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_rid [0:0]
wire   [63:0] i_host_axi_rdata;          // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_rdata [63:0]
wire   [1:0] i_host_axi_rresp;           // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_rresp [1:0]
wire   i_host_axi_rlast;                 // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_rlast
wire   i_host_axi_awready;               // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_awready
wire   i_host_axi_wready;                // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_wready
wire   i_host_axi_bvalid;                // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_bvalid
wire   [0:0] i_host_axi_bid;             // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_bid [0:0]
wire   [1:0] i_host_axi_bresp;           // core_sys > core_sys_stub -- core_sys.alb_mss_fab.host_axi_bresp [1:0]

// Instantiation of module core_sys
core_sys icore_sys(
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
  , .arcsync_axi_clk               (arcsync_axi_clk) // <   outside-of-hierarchy
  , .arcsync_axi_rst_a             (arcsync_axi_rst_a) // <   outside-of-hierarchy
  , .arcsync_core_iso_override     (arcsync_core_iso_override) // <   outside-of-hierarchy
  , .arcsync_clk                   (arcsync_clk)   // <   outside-of-hierarchy
  , .arcsync_rst_a                 (arcsync_rst_a) // <   outside-of-hierarchy
  , .host_axi_arid                 (i_host_axi_arid) // <   core_sys_stub
  , .host_axi_arvalid              (i_host_axi_arvalid) // <   core_sys_stub
  , .host_axi_araddr               (i_host_axi_araddr) // <   core_sys_stub
  , .host_axi_arburst              (i_host_axi_arburst) // <   core_sys_stub
  , .host_axi_arsize               (i_host_axi_arsize) // <   core_sys_stub
  , .host_axi_arlock               (i_host_axi_arlock) // <   core_sys_stub
  , .host_axi_arlen                (i_host_axi_arlen) // <   core_sys_stub
  , .host_axi_arcache              (i_host_axi_arcache) // <   core_sys_stub
  , .host_axi_arprot               (i_host_axi_arprot) // <   core_sys_stub
  , .host_axi_rready               (i_host_axi_rready) // <   core_sys_stub
  , .host_axi_awid                 (i_host_axi_awid) // <   core_sys_stub
  , .host_axi_awvalid              (i_host_axi_awvalid) // <   core_sys_stub
  , .host_axi_awaddr               (i_host_axi_awaddr) // <   core_sys_stub
  , .host_axi_awburst              (i_host_axi_awburst) // <   core_sys_stub
  , .host_axi_awsize               (i_host_axi_awsize) // <   core_sys_stub
  , .host_axi_awlock               (i_host_axi_awlock) // <   core_sys_stub
  , .host_axi_awlen                (i_host_axi_awlen) // <   core_sys_stub
  , .host_axi_awcache              (i_host_axi_awcache) // <   core_sys_stub
  , .host_axi_awprot               (i_host_axi_awprot) // <   core_sys_stub
  , .host_axi_wvalid               (i_host_axi_wvalid) // <   core_sys_stub
  , .host_axi_wdata                (i_host_axi_wdata) // <   core_sys_stub
  , .host_axi_wstrb                (i_host_axi_wstrb) // <   core_sys_stub
  , .host_axi_wlast                (i_host_axi_wlast) // <   core_sys_stub
  , .host_axi_bready               (i_host_axi_bready) // <   core_sys_stub
  , .bri4tb_arid                   (bri4tb_arid)   // <   outside-of-hierarchy
  , .bri4tb_arvalid                (bri4tb_arvalid) // <   outside-of-hierarchy
  , .bri4tb_araddr                 (bri4tb_araddr) // <   outside-of-hierarchy
  , .bri4tb_arburst                (bri4tb_arburst) // <   outside-of-hierarchy
  , .bri4tb_arsize                 (bri4tb_arsize) // <   outside-of-hierarchy
  , .bri4tb_arlen                  (bri4tb_arlen)  // <   outside-of-hierarchy
  , .bri4tb_arcache                (bri4tb_arcache) // <   outside-of-hierarchy
  , .bri4tb_arprot                 (bri4tb_arprot) // <   outside-of-hierarchy
  , .bri4tb_rready                 (bri4tb_rready) // <   outside-of-hierarchy
  , .bri4tb_awid                   (bri4tb_awid)   // <   outside-of-hierarchy
  , .bri4tb_awvalid                (bri4tb_awvalid) // <   outside-of-hierarchy
  , .bri4tb_awaddr                 (bri4tb_awaddr) // <   outside-of-hierarchy
  , .bri4tb_awburst                (bri4tb_awburst) // <   outside-of-hierarchy
  , .bri4tb_awsize                 (bri4tb_awsize) // <   outside-of-hierarchy
  , .bri4tb_awlen                  (bri4tb_awlen)  // <   outside-of-hierarchy
  , .bri4tb_awcache                (bri4tb_awcache) // <   outside-of-hierarchy
  , .bri4tb_awprot                 (bri4tb_awprot) // <   outside-of-hierarchy
  , .bri4tb_wid                    (bri4tb_wid)    // <   outside-of-hierarchy
  , .bri4tb_wvalid                 (bri4tb_wvalid) // <   outside-of-hierarchy
  , .bri4tb_wdata                  (bri4tb_wdata)  // <   outside-of-hierarchy
  , .bri4tb_wstrb                  (bri4tb_wstrb)  // <   outside-of-hierarchy
  , .bri4tb_wlast                  (bri4tb_wlast)  // <   outside-of-hierarchy
  , .bri4tb_bready                 (bri4tb_bready) // <   outside-of-hierarchy
  , .clk                           (clk)           // <   outside-of-hierarchy
  , .mss_clk                       (mss_clk)       // <   outside-of-hierarchy
  , .mss_fab_mst0_clk_en           (mss_fab_mst0_clk_en) // <   outside-of-hierarchy
  , .mss_fab_mst1_clk_en           (mss_fab_mst1_clk_en) // <   outside-of-hierarchy
  , .mss_fab_mst2_clk_en           (mss_fab_mst2_clk_en) // <   outside-of-hierarchy
  , .mss_fab_mst3_clk_en           (mss_fab_mst3_clk_en) // <   outside-of-hierarchy
  , .mss_fab_mst4_clk_en           (mss_fab_mst4_clk_en) // <   outside-of-hierarchy
  , .mss_fab_mst5_clk_en           (mss_fab_mst5_clk_en) // <   outside-of-hierarchy
  , .mss_fab_mst6_clk_en           (mss_fab_mst6_clk_en) // <   outside-of-hierarchy
  , .mss_fab_slv0_clk_en           (mss_fab_slv0_clk_en) // <   outside-of-hierarchy
  , .mss_fab_slv1_clk_en           (mss_fab_slv1_clk_en) // <   outside-of-hierarchy
  , .mss_fab_slv2_clk_en           (mss_fab_slv2_clk_en) // <   outside-of-hierarchy
  , .mss_fab_slv3_clk_en           (mss_fab_slv3_clk_en) // <   outside-of-hierarchy
  , .rst_b                         (rst_b)         // <   outside-of-hierarchy
  , .npu_mst1_axi_arsid            (i_npu_mst1_axi_arsid) //   > core_sys_stub
  , .npu_mst1_axi_arssid           (i_npu_mst1_axi_arssid) //   > core_sys_stub
  , .npu_mst1_axi_awsid            (i_npu_mst1_axi_awsid) //   > core_sys_stub
  , .npu_mst1_axi_awssid           (i_npu_mst1_axi_awssid) //   > core_sys_stub
  , .npu_mst2_axi_arsid            (i_npu_mst2_axi_arsid) //   > core_sys_stub
  , .npu_mst2_axi_arssid           (i_npu_mst2_axi_arssid) //   > core_sys_stub
  , .npu_mst2_axi_awsid            (i_npu_mst2_axi_awsid) //   > core_sys_stub
  , .npu_mst2_axi_awssid           (i_npu_mst2_axi_awssid) //   > core_sys_stub
  , .npu_mst3_axi_arsid            (i_npu_mst3_axi_arsid) //   > core_sys_stub
  , .npu_mst3_axi_arssid           (i_npu_mst3_axi_arssid) //   > core_sys_stub
  , .npu_mst3_axi_awsid            (i_npu_mst3_axi_awsid) //   > core_sys_stub
  , .npu_mst3_axi_awssid           (i_npu_mst3_axi_awssid) //   > core_sys_stub
  , .npu_mst4_axi_arsid            (i_npu_mst4_axi_arsid) //   > core_sys_stub
  , .npu_mst4_axi_arssid           (i_npu_mst4_axi_arssid) //   > core_sys_stub
  , .npu_mst4_axi_awsid            (i_npu_mst4_axi_awsid) //   > core_sys_stub
  , .npu_mst4_axi_awssid           (i_npu_mst4_axi_awssid) //   > core_sys_stub
  , .sl0_ecc_sbe                   (i_sl0_ecc_sbe) //   > core_sys_stub
  , .sl0_ecc_dbe                   (i_sl0_ecc_dbe) //   > core_sys_stub
  , .sl1_ecc_sbe                   (i_sl1_ecc_sbe) //   > core_sys_stub
  , .sl1_ecc_dbe                   (i_sl1_ecc_dbe) //   > core_sys_stub
  , .sl2_ecc_sbe                   (i_sl2_ecc_sbe) //   > core_sys_stub
  , .sl2_ecc_dbe                   (i_sl2_ecc_dbe) //   > core_sys_stub
  , .sl3_ecc_sbe                   (i_sl3_ecc_sbe) //   > core_sys_stub
  , .sl3_ecc_dbe                   (i_sl3_ecc_dbe) //   > core_sys_stub
  , .sl4_ecc_sbe                   (i_sl4_ecc_sbe) //   > core_sys_stub
  , .sl4_ecc_dbe                   (i_sl4_ecc_dbe) //   > core_sys_stub
  , .sl5_ecc_sbe                   (i_sl5_ecc_sbe) //   > core_sys_stub
  , .sl5_ecc_dbe                   (i_sl5_ecc_dbe) //   > core_sys_stub
  , .sl6_ecc_sbe                   (i_sl6_ecc_sbe) //   > core_sys_stub
  , .sl6_ecc_dbe                   (i_sl6_ecc_dbe) //   > core_sys_stub
  , .sl7_ecc_sbe                   (i_sl7_ecc_sbe) //   > core_sys_stub
  , .sl7_ecc_dbe                   (i_sl7_ecc_dbe) //   > core_sys_stub
  , .sl8_ecc_sbe                   (i_sl8_ecc_sbe) //   > core_sys_stub
  , .sl8_ecc_dbe                   (i_sl8_ecc_dbe) //   > core_sys_stub
  , .sl9_ecc_sbe                   (i_sl9_ecc_sbe) //   > core_sys_stub
  , .sl9_ecc_dbe                   (i_sl9_ecc_dbe) //   > core_sys_stub
  , .sl10_ecc_sbe                  (i_sl10_ecc_sbe) //   > core_sys_stub
  , .sl10_ecc_dbe                  (i_sl10_ecc_dbe) //   > core_sys_stub
  , .sl11_ecc_sbe                  (i_sl11_ecc_sbe) //   > core_sys_stub
  , .sl11_ecc_dbe                  (i_sl11_ecc_dbe) //   > core_sys_stub
  , .sl12_ecc_sbe                  (i_sl12_ecc_sbe) //   > core_sys_stub
  , .sl12_ecc_dbe                  (i_sl12_ecc_dbe) //   > core_sys_stub
  , .sl13_ecc_sbe                  (i_sl13_ecc_sbe) //   > core_sys_stub
  , .sl13_ecc_dbe                  (i_sl13_ecc_dbe) //   > core_sys_stub
  , .sl14_ecc_sbe                  (i_sl14_ecc_sbe) //   > core_sys_stub
  , .sl14_ecc_dbe                  (i_sl14_ecc_dbe) //   > core_sys_stub
  , .sl15_ecc_sbe                  (i_sl15_ecc_sbe) //   > core_sys_stub
  , .sl15_ecc_dbe                  (i_sl15_ecc_dbe) //   > core_sys_stub
  , .grp0_scm_dbank_sbe            (i_grp0_scm_dbank_sbe) //   > core_sys_stub
  , .grp0_scm_dbank_dbe            (i_grp0_scm_dbank_dbe) //   > core_sys_stub
  , .grp1_scm_dbank_sbe            (i_grp1_scm_dbank_sbe) //   > core_sys_stub
  , .grp1_scm_dbank_dbe            (i_grp1_scm_dbank_dbe) //   > core_sys_stub
  , .grp2_scm_dbank_sbe            (i_grp2_scm_dbank_sbe) //   > core_sys_stub
  , .grp2_scm_dbank_dbe            (i_grp2_scm_dbank_dbe) //   > core_sys_stub
  , .grp3_scm_dbank_sbe            (i_grp3_scm_dbank_sbe) //   > core_sys_stub
  , .grp3_scm_dbank_dbe            (i_grp3_scm_dbank_dbe) //   > core_sys_stub
  , .nl2arc0_ecc_sbe               (i_nl2arc0_ecc_sbe) //   > core_sys_stub
  , .nl2arc0_ecc_dbe               (i_nl2arc0_ecc_dbe) //   > core_sys_stub
  , .nl2arc1_ecc_sbe               (i_nl2arc1_ecc_sbe) //   > core_sys_stub
  , .nl2arc1_ecc_dbe               (i_nl2arc1_ecc_dbe) //   > core_sys_stub
  , .host_axi_arready              (i_host_axi_arready) //   > core_sys_stub
  , .host_axi_rvalid               (i_host_axi_rvalid) //   > core_sys_stub
  , .host_axi_rid                  (i_host_axi_rid) //   > core_sys_stub
  , .host_axi_rdata                (i_host_axi_rdata) //   > core_sys_stub
  , .host_axi_rresp                (i_host_axi_rresp) //   > core_sys_stub
  , .host_axi_rlast                (i_host_axi_rlast) //   > core_sys_stub
  , .host_axi_awready              (i_host_axi_awready) //   > core_sys_stub
  , .host_axi_wready               (i_host_axi_wready) //   > core_sys_stub
  , .host_axi_bvalid               (i_host_axi_bvalid) //   > core_sys_stub
  , .host_axi_bid                  (i_host_axi_bid) //   > core_sys_stub
  , .host_axi_bresp                (i_host_axi_bresp) //   > core_sys_stub
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
  , .bri4tb_arready                (bri4tb_arready) //   > outside-of-hierarchy
  , .bri4tb_rid                    (bri4tb_rid)    //   > outside-of-hierarchy
  , .bri4tb_rvalid                 (bri4tb_rvalid) //   > outside-of-hierarchy
  , .bri4tb_rdata                  (bri4tb_rdata)  //   > outside-of-hierarchy
  , .bri4tb_rresp                  (bri4tb_rresp)  //   > outside-of-hierarchy
  , .bri4tb_rlast                  (bri4tb_rlast)  //   > outside-of-hierarchy
  , .bri4tb_awready                (bri4tb_awready) //   > outside-of-hierarchy
  , .bri4tb_wready                 (bri4tb_wready) //   > outside-of-hierarchy
  , .bri4tb_bid                    (bri4tb_bid)    //   > outside-of-hierarchy
  , .bri4tb_bvalid                 (bri4tb_bvalid) //   > outside-of-hierarchy
  , .bri4tb_bresp                  (bri4tb_bresp)  //   > outside-of-hierarchy
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

// Instantiation of module core_sys_stub
core_sys_stub icore_sys_stub(
    .npu_mst1_axi_arsid  (i_npu_mst1_axi_arsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst1_axi_arssid (i_npu_mst1_axi_arssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst1_axi_awsid  (i_npu_mst1_axi_awsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst1_axi_awssid (i_npu_mst1_axi_awssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst2_axi_arsid  (i_npu_mst2_axi_arsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst2_axi_arssid (i_npu_mst2_axi_arssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst2_axi_awsid  (i_npu_mst2_axi_awsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst2_axi_awssid (i_npu_mst2_axi_awssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst3_axi_arsid  (i_npu_mst3_axi_arsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst3_axi_arssid (i_npu_mst3_axi_arssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst3_axi_awsid  (i_npu_mst3_axi_awsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst3_axi_awssid (i_npu_mst3_axi_awssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst4_axi_arsid  (i_npu_mst4_axi_arsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst4_axi_arssid (i_npu_mst4_axi_arssid)   // <   core_sys.core_archipelago.npu_top
  , .npu_mst4_axi_awsid  (i_npu_mst4_axi_awsid)    // <   core_sys.core_archipelago.npu_top
  , .npu_mst4_axi_awssid (i_npu_mst4_axi_awssid)   // <   core_sys.core_archipelago.npu_top
  , .sl0_ecc_sbe         (i_sl0_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl0_ecc_dbe         (i_sl0_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl1_ecc_sbe         (i_sl1_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl1_ecc_dbe         (i_sl1_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl2_ecc_sbe         (i_sl2_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl2_ecc_dbe         (i_sl2_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl3_ecc_sbe         (i_sl3_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl3_ecc_dbe         (i_sl3_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl4_ecc_sbe         (i_sl4_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl4_ecc_dbe         (i_sl4_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl5_ecc_sbe         (i_sl5_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl5_ecc_dbe         (i_sl5_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl6_ecc_sbe         (i_sl6_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl6_ecc_dbe         (i_sl6_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl7_ecc_sbe         (i_sl7_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl7_ecc_dbe         (i_sl7_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl8_ecc_sbe         (i_sl8_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl8_ecc_dbe         (i_sl8_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl9_ecc_sbe         (i_sl9_ecc_sbe)           // <   core_sys.core_archipelago.npu_top
  , .sl9_ecc_dbe         (i_sl9_ecc_dbe)           // <   core_sys.core_archipelago.npu_top
  , .sl10_ecc_sbe        (i_sl10_ecc_sbe)          // <   core_sys.core_archipelago.npu_top
  , .sl10_ecc_dbe        (i_sl10_ecc_dbe)          // <   core_sys.core_archipelago.npu_top
  , .sl11_ecc_sbe        (i_sl11_ecc_sbe)          // <   core_sys.core_archipelago.npu_top
  , .sl11_ecc_dbe        (i_sl11_ecc_dbe)          // <   core_sys.core_archipelago.npu_top
  , .sl12_ecc_sbe        (i_sl12_ecc_sbe)          // <   core_sys.core_archipelago.npu_top
  , .sl12_ecc_dbe        (i_sl12_ecc_dbe)          // <   core_sys.core_archipelago.npu_top
  , .sl13_ecc_sbe        (i_sl13_ecc_sbe)          // <   core_sys.core_archipelago.npu_top
  , .sl13_ecc_dbe        (i_sl13_ecc_dbe)          // <   core_sys.core_archipelago.npu_top
  , .sl14_ecc_sbe        (i_sl14_ecc_sbe)          // <   core_sys.core_archipelago.npu_top
  , .sl14_ecc_dbe        (i_sl14_ecc_dbe)          // <   core_sys.core_archipelago.npu_top
  , .sl15_ecc_sbe        (i_sl15_ecc_sbe)          // <   core_sys.core_archipelago.npu_top
  , .sl15_ecc_dbe        (i_sl15_ecc_dbe)          // <   core_sys.core_archipelago.npu_top
  , .grp0_scm_dbank_sbe  (i_grp0_scm_dbank_sbe)    // <   core_sys.core_archipelago.npu_top
  , .grp0_scm_dbank_dbe  (i_grp0_scm_dbank_dbe)    // <   core_sys.core_archipelago.npu_top
  , .grp1_scm_dbank_sbe  (i_grp1_scm_dbank_sbe)    // <   core_sys.core_archipelago.npu_top
  , .grp1_scm_dbank_dbe  (i_grp1_scm_dbank_dbe)    // <   core_sys.core_archipelago.npu_top
  , .grp2_scm_dbank_sbe  (i_grp2_scm_dbank_sbe)    // <   core_sys.core_archipelago.npu_top
  , .grp2_scm_dbank_dbe  (i_grp2_scm_dbank_dbe)    // <   core_sys.core_archipelago.npu_top
  , .grp3_scm_dbank_sbe  (i_grp3_scm_dbank_sbe)    // <   core_sys.core_archipelago.npu_top
  , .grp3_scm_dbank_dbe  (i_grp3_scm_dbank_dbe)    // <   core_sys.core_archipelago.npu_top
  , .nl2arc0_ecc_sbe     (i_nl2arc0_ecc_sbe)       // <   core_sys.core_archipelago.npu_top
  , .nl2arc0_ecc_dbe     (i_nl2arc0_ecc_dbe)       // <   core_sys.core_archipelago.npu_top
  , .nl2arc1_ecc_sbe     (i_nl2arc1_ecc_sbe)       // <   core_sys.core_archipelago.npu_top
  , .nl2arc1_ecc_dbe     (i_nl2arc1_ecc_dbe)       // <   core_sys.core_archipelago.npu_top
  , .host_axi_arready    (i_host_axi_arready)      // <   core_sys.alb_mss_fab
  , .host_axi_rvalid     (i_host_axi_rvalid)       // <   core_sys.alb_mss_fab
  , .host_axi_rid        (i_host_axi_rid)          // <   core_sys.alb_mss_fab
  , .host_axi_rdata      (i_host_axi_rdata)        // <   core_sys.alb_mss_fab
  , .host_axi_rresp      (i_host_axi_rresp)        // <   core_sys.alb_mss_fab
  , .host_axi_rlast      (i_host_axi_rlast)        // <   core_sys.alb_mss_fab
  , .host_axi_awready    (i_host_axi_awready)      // <   core_sys.alb_mss_fab
  , .host_axi_wready     (i_host_axi_wready)       // <   core_sys.alb_mss_fab
  , .host_axi_bvalid     (i_host_axi_bvalid)       // <   core_sys.alb_mss_fab
  , .host_axi_bid        (i_host_axi_bid)          // <   core_sys.alb_mss_fab
  , .host_axi_bresp      (i_host_axi_bresp)        // <   core_sys.alb_mss_fab
  , .mss_clk             (mss_clk)                 // <   outside-of-hierarchy
  , .arcsync_clk         (arcsync_clk)             // <   outside-of-hierarchy
  , .arcsync_rst_a       (arcsync_rst_a)           // <   outside-of-hierarchy
  , .host_axi_arid       (i_host_axi_arid)         //   > core_sys
  , .host_axi_arvalid    (i_host_axi_arvalid)      //   > core_sys
  , .host_axi_araddr     (i_host_axi_araddr)       //   > core_sys
  , .host_axi_arburst    (i_host_axi_arburst)      //   > core_sys
  , .host_axi_arsize     (i_host_axi_arsize)       //   > core_sys
  , .host_axi_arlock     (i_host_axi_arlock)       //   > core_sys
  , .host_axi_arlen      (i_host_axi_arlen)        //   > core_sys
  , .host_axi_arcache    (i_host_axi_arcache)      //   > core_sys
  , .host_axi_arprot     (i_host_axi_arprot)       //   > core_sys
  , .host_axi_rready     (i_host_axi_rready)       //   > core_sys
  , .host_axi_awid       (i_host_axi_awid)         //   > core_sys
  , .host_axi_awvalid    (i_host_axi_awvalid)      //   > core_sys
  , .host_axi_awaddr     (i_host_axi_awaddr)       //   > core_sys
  , .host_axi_awburst    (i_host_axi_awburst)      //   > core_sys
  , .host_axi_awsize     (i_host_axi_awsize)       //   > core_sys
  , .host_axi_awlock     (i_host_axi_awlock)       //   > core_sys
  , .host_axi_awlen      (i_host_axi_awlen)        //   > core_sys
  , .host_axi_awcache    (i_host_axi_awcache)      //   > core_sys
  , .host_axi_awprot     (i_host_axi_awprot)       //   > core_sys
  , .host_axi_wvalid     (i_host_axi_wvalid)       //   > core_sys
  , .host_axi_wdata      (i_host_axi_wdata)        //   > core_sys
  , .host_axi_wstrb      (i_host_axi_wstrb)        //   > core_sys
  , .host_axi_wlast      (i_host_axi_wlast)        //   > core_sys
  , .host_axi_bready     (i_host_axi_bready)       //   > core_sys
  );
endmodule
