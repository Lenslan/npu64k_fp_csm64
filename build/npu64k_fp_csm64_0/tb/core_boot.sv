`include "npu_defines.v"
`include "arcsync_defines.v"
`include "tb_defines.sv"


`include "npu_tb_pkg.sv"

module core_boot(
  input clk,
  input rst_a
);

  localparam CORE_NUM  = `ARCSYNC_NUM_CLUSTER * `ARCSYNC_MAX_CORES_PER_CL;
  logic arcsync_done;

  task proc_reg_read(longint addr, output int res);
    logic [39:0] a;
    longint unsigned ua;
    a = addr[39:0];
    ua = addr;

    begin
      logic [2:2]  alsb;
      // LBU access
      alsb = a[2:2];
      force `CORE_SYS_STUB.host_axi_arvalid = 1'b1;
      force `CORE_SYS_STUB.host_axi_rready  = 1'b1;
      force `CORE_SYS_STUB.host_axi_arsize  = 2;
      force `CORE_SYS_STUB.host_axi_araddr  = ua;
      @(posedge `CORE_SYS_STUB.mss_clk);
      while (!`CORE_SYS_STUB.host_axi_arready)
        @(posedge `CORE_SYS_STUB.mss_clk);
      release `CORE_SYS_STUB.host_axi_arvalid;
      release `CORE_SYS_STUB.host_axi_arsize;
      release `CORE_SYS_STUB.host_axi_araddr;
      while (!`CORE_SYS_STUB.host_axi_rvalid)
        @(posedge `CORE_SYS_STUB.mss_clk);
      release `CORE_SYS_STUB.host_axi_rready;
      res = `CORE_SYS_STUB.host_axi_rdata[alsb*32+:32];
    end
  endtask : proc_reg_read

  task proc_reg_write(longint addr, input int data);
    logic [39:0] a;
    longint unsigned  ua;
    a = addr[39:0];
    ua = addr;
    begin
      // LBU access
      logic [2:2] alsb;
      logic [7:0] strb;

      alsb = a[2:2];
      force `CORE_SYS_STUB.host_axi_awvalid = 1'b1;
      force `CORE_SYS_STUB.host_axi_awaddr  = ua;
      force `CORE_SYS_STUB.host_axi_awsize  = 2;
      force `CORE_SYS_STUB.host_axi_wvalid  = 1'b1;
      force `CORE_SYS_STUB.host_axi_bready  = 1'b1;
      if(alsb)
        force `CORE_SYS_STUB.host_axi_wdata[32*1+:32] = data;
      else
        force `CORE_SYS_STUB.host_axi_wdata[32*0+:32] = data;
      strb = 0;
      strb[alsb*4+:4] = 4'b1111;
      force `CORE_SYS_STUB.host_axi_wstrb = strb;
      force `CORE_SYS_STUB.host_axi_wlast  = 1'b1;
      @(posedge `CORE_SYS_STUB.mss_clk);
      while (!`CORE_SYS_STUB.host_axi_awready)
        @(posedge `CORE_SYS_STUB.mss_clk);
      release `CORE_SYS_STUB.host_axi_awvalid;
      release `CORE_SYS_STUB.host_axi_awaddr;
      release `CORE_SYS_STUB.host_axi_awsize;
      while (!`CORE_SYS_STUB.host_axi_wready)
        @(posedge `CORE_SYS_STUB.mss_clk);
      release `CORE_SYS_STUB.host_axi_wvalid;
      release `CORE_SYS_STUB.host_axi_wdata;
      release `CORE_SYS_STUB.host_axi_wstrb;
      release `CORE_SYS_STUB.host_axi_wlast;
      while (!`CORE_SYS_STUB.host_axi_bvalid)
        @(posedge `CORE_SYS_STUB.mss_clk);      
      release `CORE_SYS_STUB.host_axi_bready;
    end
  endtask : proc_reg_write

  task set_intvect(int core_id, longint data);
    longint addr;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_BOOT_IVB_LO + core_id * 4;
    proc_reg_write(addr, data[31:0]);
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_BOOT_IVB_HI + core_id * 4;
    proc_reg_write(addr, data[63:32]);
  endtask: set_intvect

  task raise_sft_rst(int core_id);
    int data;
    longint addr;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_RESET + core_id * 4;
    data = 'h5A5A0000 | (core_id & 'hFFFF);
    proc_reg_write(addr, data);
    
    //poll to confirm reset is completed
    while (data != 0) begin
      @(posedge clk);
      proc_reg_read(addr, data);
    end
  endtask: raise_sft_rst

  task assert_core_reset (int core_id);
    int data;
    longint addr;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_RESET + core_id * 4;
    data = 'h5A5A0000 | (core_id & 'hFFFF);
    proc_reg_write(addr, data);
    repeat (4) @(posedge clk);
  endtask: assert_core_reset

  task deassert_core_reset (int core_id);
    int data;
    longint addr;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_RESET + core_id * 4;
    data = 'hA5A50000 | (core_id & 'hFFFF);
    proc_reg_write(addr, data);
  endtask: deassert_core_reset

  task assert_grp_reset (int clusternum, int grp_code);
    longint addr;
    int status;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CL_GRP_RESET +  clusternum * 4;
    if (grp_code==5) // L2 group
      proc_reg_write(addr, ((32'h5A5A0000) | (grp_code)));
    else // L1 slice group
      proc_reg_write(addr, ((32'h5A5A0000) | (grp_code<<(grp_code*3))));
  endtask: assert_grp_reset

  task deassert_grp_reset (int clusternum, int grp_code);
    longint addr;
    int status;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CL_GRP_RESET +  clusternum * 4;
    if (grp_code==5) // L2 group
      proc_reg_write(addr, ((32'hA5A50000) | (grp_code)));
    else // L1 slice group
      proc_reg_write(addr, ((32'hA5A50000) | (grp_code<<(grp_code*3))));
  endtask: deassert_grp_reset

  task raise_run_req(int core_id);
    longint addr;
    int status;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_RUN + core_id * 4;
    proc_reg_write(addr, 1);
    
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_STATUS + core_id * 4;
    while(status & 'h7) begin
        @(posedge clk);
        proc_reg_read(addr, status);
    end
  endtask: raise_run_req

  task raise_halt_req(int core_id);
    logic[39:0] addr;
    int status;
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_HALT + core_id * 4;
    proc_reg_write(addr, 1);
    
    addr = (`ARCSYNC_BASE_ADDR<<12) + `ADDR_CORE_STATUS + core_id * 4;
    proc_reg_read(addr, status);
    while((status & 'h1) != 'h1) begin
        @(posedge clk);
        proc_reg_read(addr, status);
    end
  endtask: raise_halt_req

  task boot_core_with_axi(int core_id, longint int_vect);
    set_intvect(core_id, int_vect);
    //raise_sft_rst(core_id);
    assert_core_reset(core_id);
    raise_run_req(core_id);

    raise_halt_req(core_id);
    raise_run_req(core_id);

  endtask: boot_core_with_axi
  
  int npx_l2_coreid  ; //cluster0(ARCSYNC_MAX_CORES_PER_CL*0): l2arc=0, sl0=1
  int npx_slc0_coreid;
  int vpx_c0_coreid  ; //cluster1(ARCSYNC_MAX_CORES_PER_CL*1): vpx c0=4, c1=5
  int vpx_c1_coreid  ;
  int host_coreid    ; //cluster2(ARCSYNC_MAX_CORES_PER_CL*2): host=8

  reg run_l2_arc, boot_l2_with_pin, boot_l2_with_axi, halt_l2_with_pin;
  reg run_l1_all, boot_l1_with_pin, boot_l1_with_axi, halt_l1_with_pin;
  reg trigger_nl2arc_irq0_a, trigger_nl2arc_irq1_a;
  reg run_slc0_arc, boot_slc0_with_pin, boot_slc0_with_axi, halt_slc0_with_pin;
  reg run_slc1_arc, boot_slc1_with_pin, boot_slc1_with_axi, halt_slc1_with_pin;
  reg run_slc2_arc, boot_slc2_with_pin, boot_slc2_with_axi, halt_slc2_with_pin;
  reg run_slc3_arc, boot_slc3_with_pin, boot_slc3_with_axi, halt_slc3_with_pin;
  reg run_slc4_arc, boot_slc4_with_pin, boot_slc4_with_axi, halt_slc4_with_pin;
  reg run_slc5_arc, boot_slc5_with_pin, boot_slc5_with_axi, halt_slc5_with_pin;
  reg run_slc6_arc, boot_slc6_with_pin, boot_slc6_with_axi, halt_slc6_with_pin;
  reg run_slc7_arc, boot_slc7_with_pin, boot_slc7_with_axi, halt_slc7_with_pin;
  reg run_slc8_arc, boot_slc8_with_pin, boot_slc8_with_axi, halt_slc8_with_pin;
  reg run_slc9_arc, boot_slc9_with_pin, boot_slc9_with_axi, halt_slc9_with_pin;
  reg run_slc10_arc, boot_slc10_with_pin, boot_slc10_with_axi, halt_slc10_with_pin;
  reg run_slc11_arc, boot_slc11_with_pin, boot_slc11_with_axi, halt_slc11_with_pin;
  reg run_slc12_arc, boot_slc12_with_pin, boot_slc12_with_axi, halt_slc12_with_pin;
  reg run_slc13_arc, boot_slc13_with_pin, boot_slc13_with_axi, halt_slc13_with_pin;
  reg run_slc14_arc, boot_slc14_with_pin, boot_slc14_with_axi, halt_slc14_with_pin;
  reg run_slc15_arc, boot_slc15_with_pin, boot_slc15_with_axi, halt_slc15_with_pin;

  initial
  begin
    arcsync_done          = 1'b0;
    run_l2_arc            = get_value_from_plusargs("RUN_L2_ARC", 0);
    boot_l2_with_pin      = get_value_from_plusargs("BOOT_L2_WITH_PIN", 0);
	halt_l2_with_pin      = get_value_from_plusargs("HALT_L2_WITH_PIN", 0);
    boot_l2_with_axi      = get_value_from_plusargs("BOOT_L2_WITH_AXI", 0);
    run_l1_all            = get_value_from_plusargs("RUN_L1_ALL", 0);
    boot_l1_with_pin      = get_value_from_plusargs("BOOT_L1_WITH_PIN", 0);
	halt_l1_with_pin      = get_value_from_plusargs("HALT_L1_WITH_PIN", 0);
    boot_l1_with_axi      = get_value_from_plusargs("BOOT_L1_WITH_AXI", 0);
	trigger_nl2arc_irq0_a = get_value_from_plusargs("PIN_IRQ0_A",0);
	trigger_nl2arc_irq1_a = get_value_from_plusargs("PIN_IRQ1_A",0);
//`if (`NPU_SLICE_NUM != 1)
//    if(run_l2_arc && boot_l2_with_pin) 
//      force `ARCSYNC_PATH.nl2arc0_intvbase = 'h1800_0000 >> 10; //start_addr is 0x1800_0000, 1KB aligned
//      `if (`DUO_L2ARC == 1)
//      force `ARCSYNC_PATH.nl2arc1_intvbase = 'h1800_0000 >> 10; //start_addr is 0x1800_0000, 1KB aligned
//      `endif
//`endif
    run_slc0_arc         = get_value_from_plusargs("RUN_SLC0_ARC", run_l1_all);
    boot_slc0_with_pin   = get_value_from_plusargs("BOOT_SLC0_WITH_PIN", boot_l1_with_pin);
	halt_slc0_with_pin   = get_value_from_plusargs("HALT_SLC0_WITH_PIN", halt_l1_with_pin);
    boot_slc0_with_axi   = get_value_from_plusargs("BOOT_SLC0_WITH_AXI", boot_l1_with_axi);
    //if(run_slc0_arc && boot_slc0_with_pin)  
    //  force `ARCSYNC_PATH.sl0nl1arc_intvbase = 0 * 'h0100_0000 >> 10;
    run_slc1_arc         = get_value_from_plusargs("RUN_SLC1_ARC", run_l1_all);
    boot_slc1_with_pin   = get_value_from_plusargs("BOOT_SLC1_WITH_PIN", boot_l1_with_pin);
	halt_slc1_with_pin   = get_value_from_plusargs("HALT_SLC1_WITH_PIN", halt_l1_with_pin);
    boot_slc1_with_axi   = get_value_from_plusargs("BOOT_SLC1_WITH_AXI", boot_l1_with_axi);
    //if(run_slc1_arc && boot_slc1_with_pin)  
    //  force `ARCSYNC_PATH.sl1nl1arc_intvbase = 1 * 'h0100_0000 >> 10;
    run_slc2_arc         = get_value_from_plusargs("RUN_SLC2_ARC", run_l1_all);
    boot_slc2_with_pin   = get_value_from_plusargs("BOOT_SLC2_WITH_PIN", boot_l1_with_pin);
	halt_slc2_with_pin   = get_value_from_plusargs("HALT_SLC2_WITH_PIN", halt_l1_with_pin);
    boot_slc2_with_axi   = get_value_from_plusargs("BOOT_SLC2_WITH_AXI", boot_l1_with_axi);
    //if(run_slc2_arc && boot_slc2_with_pin)  
    //  force `ARCSYNC_PATH.sl2nl1arc_intvbase = 2 * 'h0100_0000 >> 10;
    run_slc3_arc         = get_value_from_plusargs("RUN_SLC3_ARC", run_l1_all);
    boot_slc3_with_pin   = get_value_from_plusargs("BOOT_SLC3_WITH_PIN", boot_l1_with_pin);
	halt_slc3_with_pin   = get_value_from_plusargs("HALT_SLC3_WITH_PIN", halt_l1_with_pin);
    boot_slc3_with_axi   = get_value_from_plusargs("BOOT_SLC3_WITH_AXI", boot_l1_with_axi);
    //if(run_slc3_arc && boot_slc3_with_pin)  
    //  force `ARCSYNC_PATH.sl3nl1arc_intvbase = 3 * 'h0100_0000 >> 10;
    run_slc4_arc         = get_value_from_plusargs("RUN_SLC4_ARC", run_l1_all);
    boot_slc4_with_pin   = get_value_from_plusargs("BOOT_SLC4_WITH_PIN", boot_l1_with_pin);
	halt_slc4_with_pin   = get_value_from_plusargs("HALT_SLC4_WITH_PIN", halt_l1_with_pin);
    boot_slc4_with_axi   = get_value_from_plusargs("BOOT_SLC4_WITH_AXI", boot_l1_with_axi);
    //if(run_slc4_arc && boot_slc4_with_pin)  
    //  force `ARCSYNC_PATH.sl4nl1arc_intvbase = 4 * 'h0100_0000 >> 10;
    run_slc5_arc         = get_value_from_plusargs("RUN_SLC5_ARC", run_l1_all);
    boot_slc5_with_pin   = get_value_from_plusargs("BOOT_SLC5_WITH_PIN", boot_l1_with_pin);
	halt_slc5_with_pin   = get_value_from_plusargs("HALT_SLC5_WITH_PIN", halt_l1_with_pin);
    boot_slc5_with_axi   = get_value_from_plusargs("BOOT_SLC5_WITH_AXI", boot_l1_with_axi);
    //if(run_slc5_arc && boot_slc5_with_pin)  
    //  force `ARCSYNC_PATH.sl5nl1arc_intvbase = 5 * 'h0100_0000 >> 10;
    run_slc6_arc         = get_value_from_plusargs("RUN_SLC6_ARC", run_l1_all);
    boot_slc6_with_pin   = get_value_from_plusargs("BOOT_SLC6_WITH_PIN", boot_l1_with_pin);
	halt_slc6_with_pin   = get_value_from_plusargs("HALT_SLC6_WITH_PIN", halt_l1_with_pin);
    boot_slc6_with_axi   = get_value_from_plusargs("BOOT_SLC6_WITH_AXI", boot_l1_with_axi);
    //if(run_slc6_arc && boot_slc6_with_pin)  
    //  force `ARCSYNC_PATH.sl6nl1arc_intvbase = 6 * 'h0100_0000 >> 10;
    run_slc7_arc         = get_value_from_plusargs("RUN_SLC7_ARC", run_l1_all);
    boot_slc7_with_pin   = get_value_from_plusargs("BOOT_SLC7_WITH_PIN", boot_l1_with_pin);
	halt_slc7_with_pin   = get_value_from_plusargs("HALT_SLC7_WITH_PIN", halt_l1_with_pin);
    boot_slc7_with_axi   = get_value_from_plusargs("BOOT_SLC7_WITH_AXI", boot_l1_with_axi);
    //if(run_slc7_arc && boot_slc7_with_pin)  
    //  force `ARCSYNC_PATH.sl7nl1arc_intvbase = 7 * 'h0100_0000 >> 10;
    run_slc8_arc         = get_value_from_plusargs("RUN_SLC8_ARC", run_l1_all);
    boot_slc8_with_pin   = get_value_from_plusargs("BOOT_SLC8_WITH_PIN", boot_l1_with_pin);
	halt_slc8_with_pin   = get_value_from_plusargs("HALT_SLC8_WITH_PIN", halt_l1_with_pin);
    boot_slc8_with_axi   = get_value_from_plusargs("BOOT_SLC8_WITH_AXI", boot_l1_with_axi);
    //if(run_slc8_arc && boot_slc8_with_pin)  
    //  force `ARCSYNC_PATH.sl8nl1arc_intvbase = 8 * 'h0100_0000 >> 10;
    run_slc9_arc         = get_value_from_plusargs("RUN_SLC9_ARC", run_l1_all);
    boot_slc9_with_pin   = get_value_from_plusargs("BOOT_SLC9_WITH_PIN", boot_l1_with_pin);
	halt_slc9_with_pin   = get_value_from_plusargs("HALT_SLC9_WITH_PIN", halt_l1_with_pin);
    boot_slc9_with_axi   = get_value_from_plusargs("BOOT_SLC9_WITH_AXI", boot_l1_with_axi);
    //if(run_slc9_arc && boot_slc9_with_pin)  
    //  force `ARCSYNC_PATH.sl9nl1arc_intvbase = 9 * 'h0100_0000 >> 10;
    run_slc10_arc         = get_value_from_plusargs("RUN_SLC10_ARC", run_l1_all);
    boot_slc10_with_pin   = get_value_from_plusargs("BOOT_SLC10_WITH_PIN", boot_l1_with_pin);
	halt_slc10_with_pin   = get_value_from_plusargs("HALT_SLC10_WITH_PIN", halt_l1_with_pin);
    boot_slc10_with_axi   = get_value_from_plusargs("BOOT_SLC10_WITH_AXI", boot_l1_with_axi);
    //if(run_slc10_arc && boot_slc10_with_pin)  
    //  force `ARCSYNC_PATH.sl10nl1arc_intvbase = 10 * 'h0100_0000 >> 10;
    run_slc11_arc         = get_value_from_plusargs("RUN_SLC11_ARC", run_l1_all);
    boot_slc11_with_pin   = get_value_from_plusargs("BOOT_SLC11_WITH_PIN", boot_l1_with_pin);
	halt_slc11_with_pin   = get_value_from_plusargs("HALT_SLC11_WITH_PIN", halt_l1_with_pin);
    boot_slc11_with_axi   = get_value_from_plusargs("BOOT_SLC11_WITH_AXI", boot_l1_with_axi);
    //if(run_slc11_arc && boot_slc11_with_pin)  
    //  force `ARCSYNC_PATH.sl11nl1arc_intvbase = 11 * 'h0100_0000 >> 10;
    run_slc12_arc         = get_value_from_plusargs("RUN_SLC12_ARC", run_l1_all);
    boot_slc12_with_pin   = get_value_from_plusargs("BOOT_SLC12_WITH_PIN", boot_l1_with_pin);
	halt_slc12_with_pin   = get_value_from_plusargs("HALT_SLC12_WITH_PIN", halt_l1_with_pin);
    boot_slc12_with_axi   = get_value_from_plusargs("BOOT_SLC12_WITH_AXI", boot_l1_with_axi);
    //if(run_slc12_arc && boot_slc12_with_pin)  
    //  force `ARCSYNC_PATH.sl12nl1arc_intvbase = 12 * 'h0100_0000 >> 10;
    run_slc13_arc         = get_value_from_plusargs("RUN_SLC13_ARC", run_l1_all);
    boot_slc13_with_pin   = get_value_from_plusargs("BOOT_SLC13_WITH_PIN", boot_l1_with_pin);
	halt_slc13_with_pin   = get_value_from_plusargs("HALT_SLC13_WITH_PIN", halt_l1_with_pin);
    boot_slc13_with_axi   = get_value_from_plusargs("BOOT_SLC13_WITH_AXI", boot_l1_with_axi);
    //if(run_slc13_arc && boot_slc13_with_pin)  
    //  force `ARCSYNC_PATH.sl13nl1arc_intvbase = 13 * 'h0100_0000 >> 10;
    run_slc14_arc         = get_value_from_plusargs("RUN_SLC14_ARC", run_l1_all);
    boot_slc14_with_pin   = get_value_from_plusargs("BOOT_SLC14_WITH_PIN", boot_l1_with_pin);
	halt_slc14_with_pin   = get_value_from_plusargs("HALT_SLC14_WITH_PIN", halt_l1_with_pin);
    boot_slc14_with_axi   = get_value_from_plusargs("BOOT_SLC14_WITH_AXI", boot_l1_with_axi);
    //if(run_slc14_arc && boot_slc14_with_pin)  
    //  force `ARCSYNC_PATH.sl14nl1arc_intvbase = 14 * 'h0100_0000 >> 10;
    run_slc15_arc         = get_value_from_plusargs("RUN_SLC15_ARC", run_l1_all);
    boot_slc15_with_pin   = get_value_from_plusargs("BOOT_SLC15_WITH_PIN", boot_l1_with_pin);
	halt_slc15_with_pin   = get_value_from_plusargs("HALT_SLC15_WITH_PIN", halt_l1_with_pin);
    boot_slc15_with_axi   = get_value_from_plusargs("BOOT_SLC15_WITH_AXI", boot_l1_with_axi);
    //if(run_slc15_arc && boot_slc15_with_pin)  
    //  force `ARCSYNC_PATH.sl15nl1arc_intvbase = 15 * 'h0100_0000 >> 10;

    npx_l2_coreid   = 0; 
    npx_slc0_coreid = 1;
    vpx_c0_coreid   = 4; 
    vpx_c1_coreid   = 5;
    host_coreid     = 8;
  end

  task boot_system();
  //`if (0) //{has_vpx
  //  `TB_TOP.c0ext_arc_run_req_a = 0;
  //  `TB_TOP.c1ext_arc_run_req_a = 0;
  //`endif
  //  `TB_TOP.nl2arc0_ext_arc_run_req_a = 0;
  //`if (`DUO_L2ARC == 1)
  //  `TB_TOP.nl2arc1_ext_arc_run_req_a = 0;
  //`endif
  //`for (16=0; 16<`NPU_SLICE_NUM; 16++)
  //  `TB_TOP.sl16nl1arc_ext_arc_run_req_a = 0;
  //`endfor


    if(run_l2_arc) // boot L2 arc
    begin
      if(boot_l2_with_axi) 
      begin
         boot_core_with_axi(npx_l2_coreid, 'h1800_0000 >> 10);//start_addr is 0x1800_0000, 1KB aligned
      end
      else if(boot_l2_with_pin)
      begin
       // // deassert cluster0, L2 group reset
       // deassert_grp_reset(0, 5);
       // for (int i=1; i<5; i++) begin
       //   // deassert cluster0, L1 slice group reset
       //   deassert_grp_reset(0, i);
       // end

       // // deassert cluster0, all core reset
       // for (int i=0; i<18; i++) begin
       //   deassert_core_reset(i);
       // end

        force `TB_TOP.nl2arc0_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.nl2arc0_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.nl2arc0_ext_arc_run_req_a;
        force `TB_TOP.nl2arc1_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.nl2arc1_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.nl2arc1_ext_arc_run_req_a;
      end
    end
  
      //wakeup slice 0
    if(run_slc0_arc) // boot slice 0 arc
    begin
      if(boot_slc0_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+0, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc0_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl0nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl0nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl0nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 1
    if(run_slc1_arc) // boot slice 1 arc
    begin
      if(boot_slc1_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+1, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc1_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl1nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl1nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl1nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 2
    if(run_slc2_arc) // boot slice 2 arc
    begin
      if(boot_slc2_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+2, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc2_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl2nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl2nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl2nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 3
    if(run_slc3_arc) // boot slice 3 arc
    begin
      if(boot_slc3_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+3, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc3_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl3nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl3nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl3nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 4
    if(run_slc4_arc) // boot slice 4 arc
    begin
      if(boot_slc4_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+4, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc4_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl4nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl4nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl4nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 5
    if(run_slc5_arc) // boot slice 5 arc
    begin
      if(boot_slc5_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+5, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc5_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl5nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl5nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl5nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 6
    if(run_slc6_arc) // boot slice 6 arc
    begin
      if(boot_slc6_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+6, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc6_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl6nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl6nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl6nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 7
    if(run_slc7_arc) // boot slice 7 arc
    begin
      if(boot_slc7_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+7, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc7_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl7nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl7nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl7nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 8
    if(run_slc8_arc) // boot slice 8 arc
    begin
      if(boot_slc8_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+8, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc8_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl8nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl8nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl8nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 9
    if(run_slc9_arc) // boot slice 9 arc
    begin
      if(boot_slc9_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+9, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc9_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl9nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl9nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl9nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 10
    if(run_slc10_arc) // boot slice 10 arc
    begin
      if(boot_slc10_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+10, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc10_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl10nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl10nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl10nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 11
    if(run_slc11_arc) // boot slice 11 arc
    begin
      if(boot_slc11_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+11, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc11_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl11nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl11nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl11nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 12
    if(run_slc12_arc) // boot slice 12 arc
    begin
      if(boot_slc12_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+12, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc12_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl12nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl12nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl12nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 13
    if(run_slc13_arc) // boot slice 13 arc
    begin
      if(boot_slc13_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+13, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc13_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl13nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl13nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl13nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 14
    if(run_slc14_arc) // boot slice 14 arc
    begin
      if(boot_slc14_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+14, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc14_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl14nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl14nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl14nl1arc_ext_arc_run_req_a ;
      end
    end
      //wakeup slice 15
    if(run_slc15_arc) // boot slice 15 arc
    begin
      if(boot_slc15_with_axi) 
      begin
         boot_core_with_axi(npx_slc0_coreid+15, 'h0100_0000 >> 10);// 1KB aligned
      end
      else if(boot_slc15_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl15nl1arc_ext_arc_run_req_a = 1;
        @(posedge `TB_TOP.sl15nl1arc_ext_arc_run_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl15nl1arc_ext_arc_run_req_a ;
      end
    end
  endtask: boot_system
 
  task halt_system();

    if(run_l2_arc) // boot L2 arc
    begin
      if(halt_l2_with_pin)
      begin
        force `TB_TOP.nl2arc0_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.nl2arc0_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.nl2arc0_ext_arc_halt_req_a;
        force `TB_TOP.nl2arc1_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.nl2arc1_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.nl2arc1_ext_arc_halt_req_a;
      end
    end
  
      //wakeup slice 0
    if(run_slc0_arc) // boot slice 0 arc
    begin
      if(halt_slc0_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl0nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl0nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl0nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 1
    if(run_slc1_arc) // boot slice 1 arc
    begin
      if(halt_slc1_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl1nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl1nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl1nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 2
    if(run_slc2_arc) // boot slice 2 arc
    begin
      if(halt_slc2_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl2nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl2nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl2nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 3
    if(run_slc3_arc) // boot slice 3 arc
    begin
      if(halt_slc3_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl3nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl3nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl3nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 4
    if(run_slc4_arc) // boot slice 4 arc
    begin
      if(halt_slc4_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl4nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl4nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl4nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 5
    if(run_slc5_arc) // boot slice 5 arc
    begin
      if(halt_slc5_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl5nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl5nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl5nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 6
    if(run_slc6_arc) // boot slice 6 arc
    begin
      if(halt_slc6_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl6nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl6nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl6nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 7
    if(run_slc7_arc) // boot slice 7 arc
    begin
      if(halt_slc7_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl7nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl7nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl7nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 8
    if(run_slc8_arc) // boot slice 8 arc
    begin
      if(halt_slc8_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl8nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl8nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl8nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 9
    if(run_slc9_arc) // boot slice 9 arc
    begin
      if(halt_slc9_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl9nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl9nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl9nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 10
    if(run_slc10_arc) // boot slice 10 arc
    begin
      if(halt_slc10_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl10nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl10nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl10nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 11
    if(run_slc11_arc) // boot slice 11 arc
    begin
      if(halt_slc11_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl11nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl11nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl11nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 12
    if(run_slc12_arc) // boot slice 12 arc
    begin
      if(halt_slc12_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl12nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl12nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl12nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 13
    if(run_slc13_arc) // boot slice 13 arc
    begin
      if(halt_slc13_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl13nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl13nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl13nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 14
    if(run_slc14_arc) // boot slice 14 arc
    begin
      if(halt_slc14_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl14nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl14nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl14nl1arc_ext_arc_halt_req_a ;
      end
    end
      //wakeup slice 15
    if(run_slc15_arc) // boot slice 15 arc
    begin
      if(halt_slc15_with_pin)
      begin
        repeat(1) @(posedge clk);
        force `TB_TOP.sl15nl1arc_ext_arc_halt_req_a = 1;
        @(posedge `TB_TOP.sl15nl1arc_ext_arc_halt_ack);
        repeat(1) @(posedge clk);
        release `TB_TOP.sl15nl1arc_ext_arc_halt_req_a ;
      end
    end
  endtask: halt_system

  task irq_pin();
      repeat(1) @(posedge clk);
	  if(trigger_nl2arc_irq0_a) begin
	      force `TB_TOP.nl2arc_irq0_a = 1;
		  fork
		      @ (posedge `L2_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
			  @ (posedge `L2_1_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
		  join
		  force `TB_TOP.nl2arc_irq0_a = 0;
	  end
      repeat(200) @(posedge clk);
	  if(trigger_nl2arc_irq1_a) begin
	      force `TB_TOP.nl2arc_irq1_a = 1;
		  fork
		      @ (posedge `L2_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
			  @ (posedge `L2_1_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
		  join
		  force `TB_TOP.nl2arc_irq1_a = 0;
	  end
  endtask: irq_pin
 
  logic rst_sync;
  always@(posedge clk)
  begin
    rst_sync <= rst_a;
  end

  //wake up ARC cores
  always @(posedge clk)
  begin
	if(`TB_TOP.u_sim_terminator.host_ok & (~arcsync_done)) begin
	    repeat(200) @(posedge clk);
	    halt_system();
	    repeat(100) @(posedge clk);
        boot_system();
        arcsync_done = 1'b1;
	end
	  if(arcsync_done)
	      irq_pin();
  end


//  `if ((1 == 0) && (`NPU_HAS_L2ARC == 1)) // {
//  //Force NPU AXI CONFIG address map
//  initial
//  begin
//    //Force L2ARC Group
//    force `L2ARC_GRP.u_mst_cfg_inst.decbase_r[0]   =   '0;
//    force `L2ARC_GRP.u_mst_cfg_inst.decsize_r[0]   =   '0;
//    force `L2ARC_GRP.u_mst_cfg_inst.decmst_r[0]    =  'h0;
//
//    force `L2ARC_GRP.u_cbu_cfg_inst.decbase_r[0]   =   '0;
//    force `L2ARC_GRP.u_cbu_cfg_inst.decsize_r[0]   =   '0;
//    force `L2ARC_GRP.u_cbu_cfg_inst.decmst_r[0]    =  'h0;
//
//  `for (16=0; 16<`NPU_NUM_GRP; 16++)
//    //Force CLN Group 16
//    //Top Matrix
//    force `CLN_GRP16.u_top_cfg_inst.decbase_r[0]     =   '0;
//    force `CLN_GRP16.u_top_cfg_inst.decsize_r[0]     =   '0;
//    force `CLN_GRP16.u_top_cfg_inst.decmst_r[0]      =  'h0;
//
//    //Bottom Matrix
//    force `CLN_GRP16.u_bot_inst.decbase_r[0]            =  'h00e0000;
//    force `CLN_GRP16.u_bot_inst.decsize_r[0]            =  'hfffe000;
//    force `CLN_GRP16.u_bot_inst.decmst_r[0]             =  `NPU_NUM_GRP+1;
//
//    force `CLN_GRP16.u_bot_inst.decbase_r[1]            =  'h00e6000;
//    force `CLN_GRP16.u_bot_inst.decsize_r[1]            =  'hfffff80;
//    force `CLN_GRP16.u_bot_inst.decmst_r[1]             =  `NPU_NUM_GRP+1;
//
//    force `CLN_GRP16.u_bot_inst.decbase_r[2]            =  'h00e6080;
//    force `CLN_GRP16.u_bot_inst.decsize_r[2]            =  'hffffffc;
//    force `CLN_GRP16.u_bot_inst.decmst_r[2]             =  `NPU_NUM_GRP+1;
//
//    force `CLN_GRP16.u_bot_inst.decbase_r[3]            =  'h0;
//    force `CLN_GRP16.u_bot_inst.decsize_r[3]            =  'h0;
//    force `CLN_GRP16.u_bot_inst.decmst_r[3]             =  `NPU_NUM_GRP;
//
//    //Remap Config
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 0]     =  'h00E6000;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 0]     =  'hFFFFF80;
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 1]     =  'h00E6000;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 1]     =  'h000007F;
//    `if (`NPU_SAFETY_LEVEL > 0)
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 0]     =  'h4;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 0]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 2]     =  'h5;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 2]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 4]     =  'h6;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 4]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 6]     =  'h7;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 6]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 8]     =  'h8;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 8]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[10]     =  'h9;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[10]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[12]     =  'hA;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[12]     =  '1; 
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[14]     =  'hB;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[14]     =  '1; 
//
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 1]     =  'h00E0084;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 1]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 3]     =  'h00E0085;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 3]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 5]     =  'h00E0484;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 5]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 7]     =  'h00E0485;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 7]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[ 9]     =  'h00E0884;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[ 9]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[11]     =  'h00E0885;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[11]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[13]     =  'h00E0C84;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[13]     =  '0;       
//    force `CLN_GRP16.u_remap_cfg_inst.decbase_r[15]     =  'h00E0C85;
//    force `CLN_GRP16.u_remap_cfg_inst.decsize_r[15]     =  '0;       
//    `endif
//
//    //CCM config
//    `for (`j=0; `j<`NPU_NUM_SLC_PER_GRP; `j++)
//    force `CLN_GRP16.u_ccm_inst.decbase_r[`j]     = 'h00e0000+unsigned'(1024*`j);
//    force `CLN_GRP16.u_ccm_inst.decsize_r[`j]     = 'hffffc00;
//    force `CLN_GRP16.u_ccm_inst.decmst_r[`j]      = `j;
//    `endfor
//
//    `let `m = 0
//    `for (`j=`NPU_NUM_SLC_PER_GRP; `j<`NPU_NUM_SLC_PER_GRP+`NPU_NUM_STU_PER_GRP; `j++)
//    force `CLN_GRP16.u_ccm_inst.decbase_r[`j]     = 'h00e6080+unsigned'(`m);
//    force `CLN_GRP16.u_ccm_inst.decsize_r[`j]     = 'hfffffff;
//    force `CLN_GRP16.u_ccm_inst.decmst_r[`j]      = `j;
//    `let `m = `m + 1
//    `endfor
//
//    `let `j = `NPU_NUM_SLC_PER_GRP+`NPU_NUM_STU_PER_GRP
//    force `CLN_GRP16.u_ccm_inst.decbase_r[`j]     = 'h00e6000;
//    force `CLN_GRP16.u_ccm_inst.decsize_r[`j]     = 'hfffff80;
//    force `CLN_GRP16.u_ccm_inst.decmst_r[`j]      = `j;
//  `endfor
//  end
//  `endif // }

endmodule
