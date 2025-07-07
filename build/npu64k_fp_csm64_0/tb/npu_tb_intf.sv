

`ifndef NPU_TB_INTF
`define NPU_TB_INTF

interface npu_tb_intf (
`ifndef IS_NPU_SLICE_TB
    output logic [11:0]       mst_rst_aperture_regid  ,
    output logic [31:0]       mst_rst_aperture_addr   ,
    output logic [31:0]       mst_rst_aperture_size   ,
    output logic [39:24]      npu_csm_base,
    output logic [39:12]      arcsync_sys_addr_base,
    output logic [39:16]      npu_sys_csm_addr_base,
    output logic [39:16]      npu_sys_periph_addr_base,
    output logic              nl2arc0_dbg_cache_rst_disable   ,
    output logic              nl2arc0_dccm_dmi_priority       ,
    output logic              nl2arc0_ext_arc_halt_req_a,
    input  logic              nl2arc0_ext_arc_halt_ack,
    input  logic              nl2arc0_ext_arc_run_ack,
    output logic              nl2arc1_dbg_cache_rst_disable   ,
    output logic              nl2arc1_dccm_dmi_priority       ,
    output logic              nl2arc1_ext_arc_halt_req_a,
    input  logic              nl2arc1_ext_arc_halt_ack,
    input  logic              nl2arc1_ext_arc_run_ack,
    output logic              sl0nl1arc_dbg_cache_rst_disable,
    output logic              sl0nl1arc_dccm_dmi_priority    ,
    output logic              sl0nl1arc_ext_arc_halt_req_a,
    input  logic              sl0nl1arc_ext_arc_halt_ack,
    input  logic              sl0nl1arc_ext_arc_run_ack,
    output logic              sl1nl1arc_dbg_cache_rst_disable,
    output logic              sl1nl1arc_dccm_dmi_priority    ,
    output logic              sl1nl1arc_ext_arc_halt_req_a,
    input  logic              sl1nl1arc_ext_arc_halt_ack,
    input  logic              sl1nl1arc_ext_arc_run_ack,
    output logic              sl2nl1arc_dbg_cache_rst_disable,
    output logic              sl2nl1arc_dccm_dmi_priority    ,
    output logic              sl2nl1arc_ext_arc_halt_req_a,
    input  logic              sl2nl1arc_ext_arc_halt_ack,
    input  logic              sl2nl1arc_ext_arc_run_ack,
    output logic              sl3nl1arc_dbg_cache_rst_disable,
    output logic              sl3nl1arc_dccm_dmi_priority    ,
    output logic              sl3nl1arc_ext_arc_halt_req_a,
    input  logic              sl3nl1arc_ext_arc_halt_ack,
    input  logic              sl3nl1arc_ext_arc_run_ack,
    output logic              sl4nl1arc_dbg_cache_rst_disable,
    output logic              sl4nl1arc_dccm_dmi_priority    ,
    output logic              sl4nl1arc_ext_arc_halt_req_a,
    input  logic              sl4nl1arc_ext_arc_halt_ack,
    input  logic              sl4nl1arc_ext_arc_run_ack,
    output logic              sl5nl1arc_dbg_cache_rst_disable,
    output logic              sl5nl1arc_dccm_dmi_priority    ,
    output logic              sl5nl1arc_ext_arc_halt_req_a,
    input  logic              sl5nl1arc_ext_arc_halt_ack,
    input  logic              sl5nl1arc_ext_arc_run_ack,
    output logic              sl6nl1arc_dbg_cache_rst_disable,
    output logic              sl6nl1arc_dccm_dmi_priority    ,
    output logic              sl6nl1arc_ext_arc_halt_req_a,
    input  logic              sl6nl1arc_ext_arc_halt_ack,
    input  logic              sl6nl1arc_ext_arc_run_ack,
    output logic              sl7nl1arc_dbg_cache_rst_disable,
    output logic              sl7nl1arc_dccm_dmi_priority    ,
    output logic              sl7nl1arc_ext_arc_halt_req_a,
    input  logic              sl7nl1arc_ext_arc_halt_ack,
    input  logic              sl7nl1arc_ext_arc_run_ack,
    output logic              sl8nl1arc_dbg_cache_rst_disable,
    output logic              sl8nl1arc_dccm_dmi_priority    ,
    output logic              sl8nl1arc_ext_arc_halt_req_a,
    input  logic              sl8nl1arc_ext_arc_halt_ack,
    input  logic              sl8nl1arc_ext_arc_run_ack,
    output logic              sl9nl1arc_dbg_cache_rst_disable,
    output logic              sl9nl1arc_dccm_dmi_priority    ,
    output logic              sl9nl1arc_ext_arc_halt_req_a,
    input  logic              sl9nl1arc_ext_arc_halt_ack,
    input  logic              sl9nl1arc_ext_arc_run_ack,
    output logic              sl10nl1arc_dbg_cache_rst_disable,
    output logic              sl10nl1arc_dccm_dmi_priority    ,
    output logic              sl10nl1arc_ext_arc_halt_req_a,
    input  logic              sl10nl1arc_ext_arc_halt_ack,
    input  logic              sl10nl1arc_ext_arc_run_ack,
    output logic              sl11nl1arc_dbg_cache_rst_disable,
    output logic              sl11nl1arc_dccm_dmi_priority    ,
    output logic              sl11nl1arc_ext_arc_halt_req_a,
    input  logic              sl11nl1arc_ext_arc_halt_ack,
    input  logic              sl11nl1arc_ext_arc_run_ack,
    output logic              sl12nl1arc_dbg_cache_rst_disable,
    output logic              sl12nl1arc_dccm_dmi_priority    ,
    output logic              sl12nl1arc_ext_arc_halt_req_a,
    input  logic              sl12nl1arc_ext_arc_halt_ack,
    input  logic              sl12nl1arc_ext_arc_run_ack,
    output logic              sl13nl1arc_dbg_cache_rst_disable,
    output logic              sl13nl1arc_dccm_dmi_priority    ,
    output logic              sl13nl1arc_ext_arc_halt_req_a,
    input  logic              sl13nl1arc_ext_arc_halt_ack,
    input  logic              sl13nl1arc_ext_arc_run_ack,
    output logic              sl14nl1arc_dbg_cache_rst_disable,
    output logic              sl14nl1arc_dccm_dmi_priority    ,
    output logic              sl14nl1arc_ext_arc_halt_req_a,
    input  logic              sl14nl1arc_ext_arc_halt_ack,
    input  logic              sl14nl1arc_ext_arc_run_ack,
    output logic              sl15nl1arc_dbg_cache_rst_disable,
    output logic              sl15nl1arc_dccm_dmi_priority    ,
    output logic              sl15nl1arc_ext_arc_halt_req_a,
    input  logic              sl15nl1arc_ext_arc_halt_ack,
    input  logic              sl15nl1arc_ext_arc_run_ack,
    output logic arcsync_core_iso_override,

`endif
    input bit clk, 
    input bit rst_a
    );

  `ifndef TB_MSS
    svt_mem npu_sys_shared_mem_0;
  `endif

    logic cfg_sysmap_done;
    logic cfg_arcsync_done;
    logic sim_done;
    logic l1l2_clk_gated;
    logic l2_clk_gated;
    logic sl0_clk_gated;
    logic sl1_clk_gated;
    logic sl2_clk_gated;
    logic sl3_clk_gated;
    logic sl4_clk_gated;
    logic sl5_clk_gated;
    logic sl6_clk_gated;
    logic sl7_clk_gated;
    logic sl8_clk_gated;
    logic sl9_clk_gated;
    logic sl10_clk_gated;
    logic sl11_clk_gated;
    logic sl12_clk_gated;
    logic sl13_clk_gated;
    logic sl14_clk_gated;
    logic sl15_clk_gated;


    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] dccm_lo_addr, dccm_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] idma_lo_addr, idma_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] odma_lo_addr, odma_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] conv_lo_addr, conv_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] gtoa_lo_addr, gtoa_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] safetyctrl_lo_addr, safetyctrl_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] rsvd_lo_addr, rsvd_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] am_lo_addr, am_hi_addr;
    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] vm_lo_addr, vm_hi_addr;


  

/*
    logic run_l2_arc;
    logic no_force_npu_l2_run_req;
    logic run_l1_all;
    logic no_force_npu_l1_run_req;
    logic run_slc0_arc;
    logic run_slc1_arc;
    logic run_slc2_arc;
    logic run_slc3_arc;
    logic run_slc4_arc;
    logic run_slc5_arc;
    logic run_slc6_arc;
    logic run_slc7_arc;
    logic run_slc8_arc;
    logic run_slc9_arc;
    logic run_slc10_arc;
    logic run_slc11_arc;
    logic run_slc12_arc;
    logic run_slc13_arc;
    logic run_slc14_arc;
    logic run_slc15_arc;
    
    function set_run_cores ();
      run_l2_arc = get_value_from_plusargs("RUN_L2_ARC", 0);
      run_l1_all = get_value_from_plusargs("RUN_L1_ALL", 0);
      no_force_npu_l2_run_req = get_value_from_plusargs("NO_FORCE_NPU_L2_RUN_REQ", 0);
      no_force_npu_l1_run_req = get_value_from_plusargs("NO_FORCE_NPU_L1_RUN_REQ", 0);
      run_slc0_arc = get_value_from_plusargs("RUN_SLC0_ARC", run_l1_all);
      run_slc1_arc = get_value_from_plusargs("RUN_SLC1_ARC", run_l1_all);
      run_slc2_arc = get_value_from_plusargs("RUN_SLC2_ARC", run_l1_all);
      run_slc3_arc = get_value_from_plusargs("RUN_SLC3_ARC", run_l1_all);
      run_slc4_arc = get_value_from_plusargs("RUN_SLC4_ARC", run_l1_all);
      run_slc5_arc = get_value_from_plusargs("RUN_SLC5_ARC", run_l1_all);
      run_slc6_arc = get_value_from_plusargs("RUN_SLC6_ARC", run_l1_all);
      run_slc7_arc = get_value_from_plusargs("RUN_SLC7_ARC", run_l1_all);
      run_slc8_arc = get_value_from_plusargs("RUN_SLC8_ARC", run_l1_all);
      run_slc9_arc = get_value_from_plusargs("RUN_SLC9_ARC", run_l1_all);
      run_slc10_arc = get_value_from_plusargs("RUN_SLC10_ARC", run_l1_all);
      run_slc11_arc = get_value_from_plusargs("RUN_SLC11_ARC", run_l1_all);
      run_slc12_arc = get_value_from_plusargs("RUN_SLC12_ARC", run_l1_all);
      run_slc13_arc = get_value_from_plusargs("RUN_SLC13_ARC", run_l1_all);
      run_slc14_arc = get_value_from_plusargs("RUN_SLC14_ARC", run_l1_all);
      run_slc15_arc = get_value_from_plusargs("RUN_SLC15_ARC", run_l1_all);
  
    endfunction
*/
endinterface: npu_tb_intf

`endif // NPU_TB_INTF
