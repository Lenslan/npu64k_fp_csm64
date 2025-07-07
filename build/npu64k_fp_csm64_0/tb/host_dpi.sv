`include "npu_defines.v"
`include "arcsync_defines.v"
`include "tb_defines.sv"
//`include "apb_master.sv"

// Host DPI model
module host_model(
    input  logic clk
  , input  logic rst_a
  , output logic sys_cfg_done
  //, input  logic arcsync_done
);

  import "DPI-C" context task host_exec();
  export "DPI-C" task host_wait;
  export "DPI-C" function host_read_byte;
  export "DPI-C" function host_read_short;
  export "DPI-C" function host_read_int;
  export "DPI-C" function host_read_long;
  export "DPI-C" function get_retd;
  export "DPI-C" task host_read;
  export "DPI-C" task host_write_byte;
  export "DPI-C" task host_write_short;
  export "DPI-C" task host_write_int;
`ifndef DW_DBP_EN
  export "DPI-C" task host_apb_write_int;
  export "DPI-C" task host_apb_read_int;
  export "DPI-C" task host_apb_db_write;
  export "DPI-C" task host_apb_db_read;
  export "DPI-C" function get_retd_apb;
`endif
  export "DPI-C" task start_async_apb_clk;
  export "DPI-C" task stop_async_apb_clk;
  export "DPI-C" task set_apb_clk;
  export "DPI-C" task host_print;
  export "DPI-C" task host_write_long;
  export "DPI-C" task host_exit;
  export "DPI-C" task host_terminate_sim;
  export "DPI-C" task force_test_ok;
  export "DPI-C" task set_sys_cfg_done;
  //export "DPI-C" task wait_arcsync_done;
  export "DPI-C" task set_expect_resp;
  export "DPI-C" task set_disable_resp_chk;

  export "DPI-C" function get_host_err;

  export "DPI-C" function get_dbgen_niden_val;
  
`ifndef DW_DBP_EN
  export "DPI-C" task wait_for_trace_swe_atb_op;
  export "DPI-C" task wait_for_trace_flush;
  export "DPI-C" function get_tcode_data;
  export "DPI-C" task check_swe_tcode_out;
`endif

   task wait_for_trace_swe_atb_op();
    @(posedge `ARCHIPELAGO.swe_atvalid);
   endtask

   task wait_for_trace_flush();
`ifndef DW_DBP_EN
    wait(`TB_TOP.i_rtt_tb.flush_complete);
    @(posedge clk) begin
    force `ARCHIPELAGO.cti_trace_start = 1;
    force `ARCHIPELAGO.cti_trace_stop  = 1;
    force `TB_TOP.i_rtt_tb.afvalid     = 1;
    force `TB_TOP.i_rtt_tb.swe_afvalid = 1;
    force `ARCHIPELAGO.arct0_dbgen  = ~`ARCHIPELAGO.arct0_dbgen;
    force `ARCHIPELAGO.arct0_niden  = ~`ARCHIPELAGO.arct0_niden;
    force `ARCHIPELAGO.nl2arc0_dbgen = ~`ARCHIPELAGO.nl2arc0_dbgen;
    force `ARCHIPELAGO.nl2arc0_niden = ~`ARCHIPELAGO.nl2arc0_niden;
    force `ARCHIPELAGO.nl2arc1_dbgen = ~`ARCHIPELAGO.nl2arc1_dbgen;
    force `ARCHIPELAGO.nl2arc1_niden = ~`ARCHIPELAGO.nl2arc1_niden;
    force `ARCHIPELAGO.sl0nl1arc_dbgen = ~`ARCHIPELAGO.sl0nl1arc_dbgen;
    force `ARCHIPELAGO.sl0nl1arc_niden = ~`ARCHIPELAGO.sl0nl1arc_niden;
    force `ARCHIPELAGO.sl1nl1arc_dbgen = ~`ARCHIPELAGO.sl1nl1arc_dbgen;
    force `ARCHIPELAGO.sl1nl1arc_niden = ~`ARCHIPELAGO.sl1nl1arc_niden;
    force `ARCHIPELAGO.sl2nl1arc_dbgen = ~`ARCHIPELAGO.sl2nl1arc_dbgen;
    force `ARCHIPELAGO.sl2nl1arc_niden = ~`ARCHIPELAGO.sl2nl1arc_niden;
    force `ARCHIPELAGO.sl3nl1arc_dbgen = ~`ARCHIPELAGO.sl3nl1arc_dbgen;
    force `ARCHIPELAGO.sl3nl1arc_niden = ~`ARCHIPELAGO.sl3nl1arc_niden;
    force `ARCHIPELAGO.sl4nl1arc_dbgen = ~`ARCHIPELAGO.sl4nl1arc_dbgen;
    force `ARCHIPELAGO.sl4nl1arc_niden = ~`ARCHIPELAGO.sl4nl1arc_niden;
    force `ARCHIPELAGO.sl5nl1arc_dbgen = ~`ARCHIPELAGO.sl5nl1arc_dbgen;
    force `ARCHIPELAGO.sl5nl1arc_niden = ~`ARCHIPELAGO.sl5nl1arc_niden;
    force `ARCHIPELAGO.sl6nl1arc_dbgen = ~`ARCHIPELAGO.sl6nl1arc_dbgen;
    force `ARCHIPELAGO.sl6nl1arc_niden = ~`ARCHIPELAGO.sl6nl1arc_niden;
    force `ARCHIPELAGO.sl7nl1arc_dbgen = ~`ARCHIPELAGO.sl7nl1arc_dbgen;
    force `ARCHIPELAGO.sl7nl1arc_niden = ~`ARCHIPELAGO.sl7nl1arc_niden;
    force `ARCHIPELAGO.sl8nl1arc_dbgen = ~`ARCHIPELAGO.sl8nl1arc_dbgen;
    force `ARCHIPELAGO.sl8nl1arc_niden = ~`ARCHIPELAGO.sl8nl1arc_niden;
    force `ARCHIPELAGO.sl9nl1arc_dbgen = ~`ARCHIPELAGO.sl9nl1arc_dbgen;
    force `ARCHIPELAGO.sl9nl1arc_niden = ~`ARCHIPELAGO.sl9nl1arc_niden;
    force `ARCHIPELAGO.sl10nl1arc_dbgen = ~`ARCHIPELAGO.sl10nl1arc_dbgen;
    force `ARCHIPELAGO.sl10nl1arc_niden = ~`ARCHIPELAGO.sl10nl1arc_niden;
    force `ARCHIPELAGO.sl11nl1arc_dbgen = ~`ARCHIPELAGO.sl11nl1arc_dbgen;
    force `ARCHIPELAGO.sl11nl1arc_niden = ~`ARCHIPELAGO.sl11nl1arc_niden;
    force `ARCHIPELAGO.sl12nl1arc_dbgen = ~`ARCHIPELAGO.sl12nl1arc_dbgen;
    force `ARCHIPELAGO.sl12nl1arc_niden = ~`ARCHIPELAGO.sl12nl1arc_niden;
    force `ARCHIPELAGO.sl13nl1arc_dbgen = ~`ARCHIPELAGO.sl13nl1arc_dbgen;
    force `ARCHIPELAGO.sl13nl1arc_niden = ~`ARCHIPELAGO.sl13nl1arc_niden;
    force `ARCHIPELAGO.sl14nl1arc_dbgen = ~`ARCHIPELAGO.sl14nl1arc_dbgen;
    force `ARCHIPELAGO.sl14nl1arc_niden = ~`ARCHIPELAGO.sl14nl1arc_niden;
    force `ARCHIPELAGO.sl15nl1arc_dbgen = ~`ARCHIPELAGO.sl15nl1arc_dbgen;
    force `ARCHIPELAGO.sl15nl1arc_niden = ~`ARCHIPELAGO.sl15nl1arc_niden;
    end
    @(posedge clk) begin
    force `ARCHIPELAGO.cti_trace_start = 0;
    force `ARCHIPELAGO.cti_trace_stop  = 0;
    force `TB_TOP.i_rtt_tb.afvalid     = 0;
    force `TB_TOP.i_rtt_tb.swe_afvalid = 0;
    force `ARCHIPELAGO.arct0_dbgen  = ~`ARCHIPELAGO.arct0_dbgen;
    force `ARCHIPELAGO.arct0_niden  = ~`ARCHIPELAGO.arct0_niden;
    force `ARCHIPELAGO.nl2arc0_dbgen = ~`ARCHIPELAGO.nl2arc0_dbgen;
    force `ARCHIPELAGO.nl2arc0_niden = ~`ARCHIPELAGO.nl2arc0_niden;
    force `ARCHIPELAGO.nl2arc1_dbgen = ~`ARCHIPELAGO.nl2arc1_dbgen;
    force `ARCHIPELAGO.nl2arc1_niden = ~`ARCHIPELAGO.nl2arc1_niden;
    force `ARCHIPELAGO.sl0nl1arc_dbgen = ~`ARCHIPELAGO.sl0nl1arc_dbgen;
    force `ARCHIPELAGO.sl0nl1arc_niden = ~`ARCHIPELAGO.sl0nl1arc_niden;
    force `ARCHIPELAGO.sl1nl1arc_dbgen = ~`ARCHIPELAGO.sl1nl1arc_dbgen;
    force `ARCHIPELAGO.sl1nl1arc_niden = ~`ARCHIPELAGO.sl1nl1arc_niden;
    force `ARCHIPELAGO.sl2nl1arc_dbgen = ~`ARCHIPELAGO.sl2nl1arc_dbgen;
    force `ARCHIPELAGO.sl2nl1arc_niden = ~`ARCHIPELAGO.sl2nl1arc_niden;
    force `ARCHIPELAGO.sl3nl1arc_dbgen = ~`ARCHIPELAGO.sl3nl1arc_dbgen;
    force `ARCHIPELAGO.sl3nl1arc_niden = ~`ARCHIPELAGO.sl3nl1arc_niden;
    force `ARCHIPELAGO.sl4nl1arc_dbgen = ~`ARCHIPELAGO.sl4nl1arc_dbgen;
    force `ARCHIPELAGO.sl4nl1arc_niden = ~`ARCHIPELAGO.sl4nl1arc_niden;
    force `ARCHIPELAGO.sl5nl1arc_dbgen = ~`ARCHIPELAGO.sl5nl1arc_dbgen;
    force `ARCHIPELAGO.sl5nl1arc_niden = ~`ARCHIPELAGO.sl5nl1arc_niden;
    force `ARCHIPELAGO.sl6nl1arc_dbgen = ~`ARCHIPELAGO.sl6nl1arc_dbgen;
    force `ARCHIPELAGO.sl6nl1arc_niden = ~`ARCHIPELAGO.sl6nl1arc_niden;
    force `ARCHIPELAGO.sl7nl1arc_dbgen = ~`ARCHIPELAGO.sl7nl1arc_dbgen;
    force `ARCHIPELAGO.sl7nl1arc_niden = ~`ARCHIPELAGO.sl7nl1arc_niden;
    force `ARCHIPELAGO.sl8nl1arc_dbgen = ~`ARCHIPELAGO.sl8nl1arc_dbgen;
    force `ARCHIPELAGO.sl8nl1arc_niden = ~`ARCHIPELAGO.sl8nl1arc_niden;
    force `ARCHIPELAGO.sl9nl1arc_dbgen = ~`ARCHIPELAGO.sl9nl1arc_dbgen;
    force `ARCHIPELAGO.sl9nl1arc_niden = ~`ARCHIPELAGO.sl9nl1arc_niden;
    force `ARCHIPELAGO.sl10nl1arc_dbgen = ~`ARCHIPELAGO.sl10nl1arc_dbgen;
    force `ARCHIPELAGO.sl10nl1arc_niden = ~`ARCHIPELAGO.sl10nl1arc_niden;
    force `ARCHIPELAGO.sl11nl1arc_dbgen = ~`ARCHIPELAGO.sl11nl1arc_dbgen;
    force `ARCHIPELAGO.sl11nl1arc_niden = ~`ARCHIPELAGO.sl11nl1arc_niden;
    force `ARCHIPELAGO.sl12nl1arc_dbgen = ~`ARCHIPELAGO.sl12nl1arc_dbgen;
    force `ARCHIPELAGO.sl12nl1arc_niden = ~`ARCHIPELAGO.sl12nl1arc_niden;
    force `ARCHIPELAGO.sl13nl1arc_dbgen = ~`ARCHIPELAGO.sl13nl1arc_dbgen;
    force `ARCHIPELAGO.sl13nl1arc_niden = ~`ARCHIPELAGO.sl13nl1arc_niden;
    force `ARCHIPELAGO.sl14nl1arc_dbgen = ~`ARCHIPELAGO.sl14nl1arc_dbgen;
    force `ARCHIPELAGO.sl14nl1arc_niden = ~`ARCHIPELAGO.sl14nl1arc_niden;
    force `ARCHIPELAGO.sl15nl1arc_dbgen = ~`ARCHIPELAGO.sl15nl1arc_dbgen;
    force `ARCHIPELAGO.sl15nl1arc_niden = ~`ARCHIPELAGO.sl15nl1arc_niden;
    end
`endif
   endtask

   function longint get_tcode_data();
`ifndef DW_DBP_EN
     get_tcode_data = `TB_TOP.i_rtt_tb.tcode_dout;
`endif
   endfunction

   task check_swe_tcode_out();
     wait(&`TB_TOP.i_rtt_tb.swe_tcode_pass);
   endtask



   function int get_dbgen_niden_val(input int index);
     if (index == 0)
       get_dbgen_niden_val = 0;
     else
     begin
      if (`TB_TOP.dbgen_niden[index][0])
       get_dbgen_niden_val[1:0] = 3;
      else
       get_dbgen_niden_val[1:0] = 2;

      if (|`TB_TOP.dbgen_niden[index])
       get_dbgen_niden_val[3:2] = 3;
      else
       get_dbgen_niden_val[3:2] = 2;
     end
   endfunction


  logic axi_user_en;
  logic host_done;
  bit   force_exit;
  logic host_ok;

  logic [63:0] retd; //return data from AXI
  logic [1:0] exp_err = 0;
  logic      dis_resp_chk = 0; 
  logic [31:0] host_err = 0;
  bit [31:0] apb_rd_data;

  task host_read(input longint addr, input int axsize);
    logic [39:0] a;
    longint unsigned ua;
    a = addr[39:0];
    ua = addr;
    retd = '0;

    begin
      logic [2:0]  alsb;
      alsb = 0;

      `CORE_SYS_STUB.host_axi_arvalid = 1'b1;
      `CORE_SYS_STUB.host_axi_rready  = 1'b1;
      `CORE_SYS_STUB.host_axi_arsize  = axsize;
      `CORE_SYS_STUB.host_axi_araddr  = ua;
      @(posedge `CORE_SYS_STUB.mss_clk);
      while (!`CORE_SYS_STUB.host_axi_arready)
        @(posedge `CORE_SYS_STUB.mss_clk);
      `CORE_SYS_STUB.host_axi_arvalid = '0;
      `CORE_SYS_STUB.host_axi_arsize  = '0;
      `CORE_SYS_STUB.host_axi_araddr  = '0;

      while (!`CORE_SYS_STUB.host_axi_rvalid)
        @(posedge `CORE_SYS_STUB.mss_clk);
      `CORE_SYS_STUB.host_axi_rready  = '0;

      case(axsize)
        0: begin
             alsb = a[2:0];
             retd = `CORE_SYS_STUB.host_axi_rdata[alsb*8+:8];
           end
        1: begin
             alsb = a[2:1];
             retd = `CORE_SYS_STUB.host_axi_rdata[alsb*16+:16];
           end
        2: begin
             alsb = a[2:2];
             retd = `CORE_SYS_STUB.host_axi_rdata[alsb*32+:32];
           end
        3: begin
             alsb = 0;
             retd = `CORE_SYS_STUB.host_axi_rdata[alsb*64+:64];
           end
        default: retd = 0;
      endcase

	    if (`CORE_SYS_STUB.host_axi_rresp != exp_err && dis_resp_chk == 0) begin
		     host_err++;
         $fatal("Read ADDR:%h, resp not expected, exp:%d, rtl:%d", addr, exp_err, `CORE_SYS_STUB.host_axi_rresp);
	    end

    end
  endtask: host_read

  task host_write(input longint addr, input longint idata, input int axsize);
    logic [39:0] a;
    longint unsigned  ua;
    logic [63:0] data;
    a    = addr[39:0];
    ua   = addr;
    data = idata;
    begin

      // LBU access
      logic [2:0] alsb;
      logic [7:0] strb;

      `CORE_SYS_STUB.host_axi_awvalid = 1'b1;
      `CORE_SYS_STUB.host_axi_awaddr  = ua;
      `CORE_SYS_STUB.host_axi_awsize  = axsize;
      `CORE_SYS_STUB.host_axi_wvalid  = 1'b1;
      `CORE_SYS_STUB.host_axi_bready  = 1'b1;

      strb = 0;
      case(axsize)
        0 : begin
              alsb = a[2:0];
              strb[alsb*1+:1]='1;
              case(alsb)
                0 : `CORE_SYS_STUB.host_axi_wdata[0*8+:8] = data;
                1 : `CORE_SYS_STUB.host_axi_wdata[1*8+:8] = data;
                2 : `CORE_SYS_STUB.host_axi_wdata[2*8+:8] = data;
                3 : `CORE_SYS_STUB.host_axi_wdata[3*8+:8] = data;
                4 : `CORE_SYS_STUB.host_axi_wdata[4*8+:8] = data;
                5 : `CORE_SYS_STUB.host_axi_wdata[5*8+:8] = data;
                6 : `CORE_SYS_STUB.host_axi_wdata[6*8+:8] = data;
                7 : `CORE_SYS_STUB.host_axi_wdata[7*8+:8] = data;
              endcase
            end
        1 : begin
              alsb = a[2:1];
              strb[alsb*2+:2]='1;
              case(alsb)
                0 : `CORE_SYS_STUB.host_axi_wdata[0*16+:16] = data;
                1 : `CORE_SYS_STUB.host_axi_wdata[1*16+:16] = data;
                2 : `CORE_SYS_STUB.host_axi_wdata[2*16+:16] = data;
                3 : `CORE_SYS_STUB.host_axi_wdata[3*16+:16] = data;
              endcase
            end
        2 : begin
              alsb = a[2:2];
              strb[alsb*4+:4]='1;
              case(alsb)
                0 : `CORE_SYS_STUB.host_axi_wdata[0*32+:32] = data;
                1 : `CORE_SYS_STUB.host_axi_wdata[1*32+:32] = data;
              endcase
            end
        3 : begin
              alsb = 0;
              strb[alsb*8+:8]='1;
              `CORE_SYS_STUB.host_axi_wdata[0+:64] = data[0+:64];
            end
      endcase

      `CORE_SYS_STUB.host_axi_wstrb  = strb;
      `CORE_SYS_STUB.host_axi_wlast  = 1'b1;
      @(posedge `CORE_SYS_STUB.mss_clk);

      while (!`CORE_SYS_STUB.host_axi_awready)
        @(posedge `CORE_SYS_STUB.mss_clk);
      `CORE_SYS_STUB.host_axi_awvalid = '0;
      `CORE_SYS_STUB.host_axi_awaddr  = '0;
      `CORE_SYS_STUB.host_axi_awsize  = '0;
      while (!`CORE_SYS_STUB.host_axi_wready)
        @(posedge `CORE_SYS_STUB.mss_clk);
      `CORE_SYS_STUB.host_axi_wvalid  = '0;
      `CORE_SYS_STUB.host_axi_wdata   = '0;
      `CORE_SYS_STUB.host_axi_wstrb   = '0;
      `CORE_SYS_STUB.host_axi_wlast   = '0;
      while (!`CORE_SYS_STUB.host_axi_bvalid)
        @(posedge `CORE_SYS_STUB.mss_clk);
      `CORE_SYS_STUB.host_axi_bready  = '0;

      if (`CORE_SYS_STUB.host_axi_bresp != exp_err && dis_resp_chk == 0) begin
		   host_err++;
       $error("resp not expected, exp:%d, rtl:%d",exp_err, `CORE_SYS_STUB.host_axi_bresp);
		   $finish;
	  end

	end
  endtask: host_write

  function longint get_retd(input longint addr);
    return retd;
  endfunction

  function longint get_retd_apb();
    return apb_rd_data;
  endfunction

  task host_wait(input int count);
    repeat (count) @ (posedge `CORE_SYS_STUB.mss_clk);
  endtask

  function byte host_read_byte(input longint addr);
    return retd[0+:8];
  endfunction

  function shortint host_read_short(input longint addr);
    return retd[0+:16];
  endfunction

  function int host_read_int(input longint addr);
    return retd[0+:32];
  endfunction

  function longint host_read_long(input longint addr);
    return retd[0+:64];
  endfunction


  task host_write_byte(input longint addr, input byte data);
    longint d;
    d = data;
    host_write(addr,d, 0);
  endtask

  task host_write_short(input longint addr, input shortint data);
    longint d;
    d = data;
    host_write(addr,d, 1);
  endtask

  task host_write_int(input longint addr, input int data);
    longint d;
    d = data;
    host_write(addr,d, 2);
  endtask

 task  host_write_long(input longint addr, input longint data);
    longint d;
    d = data;
    host_write(addr,d, 3);
  endtask

  task host_exit(int err_cnt=0);
    @(posedge clk);
    host_done = 1;
    host_ok = err_cnt == 0;

    if(err_cnt == 0) $display("Host finished config successfully");
    else $display("Host run with error(s)");

  endtask: host_exit

  function int get_host_err();
   get_host_err = host_err;
  endfunction


  task set_expect_resp(input int v=0);
    @(posedge clk);
    exp_err = v;

    $info("set expect response test:%d",exp_err);
  endtask: set_expect_resp


  task set_disable_resp_chk(input int v=0);
    @(posedge clk);
    dis_resp_chk = v;

    $info("set disable response check:%d",dis_resp_chk);
  endtask: set_disable_resp_chk


  task host_terminate_sim();
    repeat (1) @(posedge clk);

    $info("Host program exits simulator");
     $finish("Host stops simulator");
  endtask: host_terminate_sim

  task force_test_ok();
    repeat (1) @(posedge clk);
    force_exit = 1;
  endtask: force_test_ok

  task set_sys_cfg_done();
    sys_cfg_done <= 1;
    repeat(10) @(posedge clk);
    sys_cfg_done <= 0;
  endtask: set_sys_cfg_done

  /*
  task wait_arcsync_done();
    while (!arcsync_done) begin
      @(posedge clk);
    end
    sys_cfg_done <= 0;
  endtask: wait_arcsync_done
  */

  //==========================================================================
  // APB Driver Logic
  //==========================================================================
    apb_master  apb_master_u0();
    assign apb_master_u0.PCLK    = clk;
    assign apb_master_u0.PRESETn = !rst_a;

    semaphore apb_bus_key    = new(1);
    semaphore db_apb_bus_key = new(1);


    async_clk_gen_if  async_apb_clk();
    assign async_apb_clk.ip_clk       = clk;

   function force_apb();
    force `ARCHIPELAGO.arct0_paddrdbg    = apb_master_u0.PADDR      ;
    force `ARCHIPELAGO.arct0_pseldbg     = apb_master_u0.PSEL       ;
    force `ARCHIPELAGO.arct0_penabledbg  = apb_master_u0.PENABLE    ;
    force `ARCHIPELAGO.arct0_pwritedbg   = apb_master_u0.PWRITE     ;
    force `ARCHIPELAGO.arct0_pwdatadbg   = apb_master_u0.PWDATA     ;

    force apb_master_u0.PREADY   =  `ARCHIPELAGO.arct0_preadydbg;
    force apb_master_u0.PRDATA   =  `ARCHIPELAGO.arct0_prdatadbg;
    force apb_master_u0.PSLVERR  =  `ARCHIPELAGO.arct0_pslverrdbg;
   endfunction

   function force_async_apb_clock();
     force apb_master_u0.PCLK     = async_apb_clk.op_clk;
     force `ARCHIPELAGO.pclkdbg   = async_apb_clk.op_clk;
   endfunction

   function release_async_apb_clock();
    release `ARCHIPELAGO.pclkdbg;
    release apb_master_u0.PCLK;
   endfunction

   function release_apb();
    release `ARCHIPELAGO.arct0_paddrdbg;
    release `ARCHIPELAGO.arct0_pseldbg;
    release `ARCHIPELAGO.arct0_penabledbg;
    release `ARCHIPELAGO.arct0_pwritedbg;
    release `ARCHIPELAGO.arct0_pwdatadbg;

    release apb_master_u0.PREADY;
    release apb_master_u0.PRDATA;
    release apb_master_u0.PSLVERR;
   endfunction


    task host_apb_write_int(input longint addr, input int data,input exp_err);
     force_apb();
     apb_bus_key.get(1);
     apb_master_u0.write_apb(addr,data);
     if (`ARCHIPELAGO.arct0_preadydbg == 0) host_err++;
     if (!`ARCHIPELAGO.arct0_pslverrdbg && exp_err == 1) host_err++;
     apb_bus_key.put(1);
     release_apb();
    endtask

    task host_apb_read_int(input longint addr,int exp_err);
     force_apb();
     apb_bus_key.get(1);
     apb_master_u0.read_apb(addr,apb_rd_data);
     if (`ARCHIPELAGO.arct0_preadydbg == 0) host_err++;
     if (`ARCHIPELAGO.arct0_pslverrdbg && exp_err == 0) host_err++;
     if (!`ARCHIPELAGO.arct0_pslverrdbg && exp_err == 1) host_err++;
     apb_bus_key.put(1);
     release_apb();
    endtask

    task host_print(input int value);
      $display($time," HOST DEBUG PRINT %0h ",value);
    endtask

    task host_apb_db_write(input int base_addr, input int db_addr,input int dbg_cmd,input int data,input int exp_err);
     force_apb();
     db_apb_bus_key.get(1);
     host_apb_write_int(base_addr+32'h02,db_addr,exp_err); // DB ADDR
     host_apb_write_int(base_addr+32'h03,data   ,exp_err); // DB DATA
     host_apb_write_int(base_addr+32'h01,dbg_cmd,exp_err); // DB CMD
     host_apb_write_int(base_addr+32'h00,data   ,exp_err); // DB STAT
     for (int i = 0; i < 100; i++)
     begin
      if (exp_err) break;
      host_apb_read_int(base_addr+32'h00,exp_err); // DB STAT
      if (apb_rd_data[2] == 1)  break;
      if (i == 99 && apb_rd_data[2] == 0 ) $error($time," APB DB Write: Did not Get Ready bit in DB STAT - Err %0d ",host_err++);
      else  if (apb_rd_data[2] == 0)  #1us;
     end
     db_apb_bus_key.put(1);
     release_apb();
    endtask

    task host_apb_db_read(input int base_addr, input int db_addr,input int dbg_cmd,input int exp_err);
     force_apb();
     db_apb_bus_key.get(1);
     host_apb_write_int(base_addr+32'h02,db_addr,exp_err); // DB ADDR
     host_apb_write_int(base_addr+32'h01,dbg_cmd,exp_err); // DB CMD
     host_apb_write_int(base_addr+32'h00,db_addr,exp_err); // DB STAT
     for (int i = 0; i < 100; i++)
     begin
      if (exp_err) break;
      host_apb_read_int(base_addr+32'h00,exp_err); // DB STAT
      if (apb_rd_data[2] == 1)  break;
      if (i == 99 && apb_rd_data[2] == 0 ) $error($time," APB DB Read: Did not Get Ready bit in DB STAT - Err %0d ",host_err++);
      else  if (apb_rd_data[2] == 0)  #1us;
     end
     host_apb_read_int (base_addr+32'h03,exp_err); // DB DATA
     db_apb_bus_key.put(1);
     release_apb();
    endtask

    task start_async_apb_clk();
     force_async_apb_clock();
     fork
      async_apb_clk.start_the_clock();
     join_none
    endtask

    task stop_async_apb_clk();
     async_apb_clk.stop = 1;
     release_async_apb_clock();
    endtask

    task set_apb_clk(input int div_mul_factor,input int div_mul);
      async_apb_clk.op_clk_div_mul_factor = div_mul_factor;
      async_apb_clk.div_mul               = div_mul;
    endtask
  //==========================================================================
  // Rascal related APIs
  typedef enum logic[3:0] {
    DBG_MEM_WRITE = 0,
    DBG_REG_WRITE = 1,
    DBG_AUX_WRITE = 2,
    DBG_CORE_RST  = 3,
    DBG_MEM_READ  = 4,
    DBG_REG_READ  = 5,
    DBG_AUX_READ  = 6
  } dbg_cmd_e;


  /////////////////////////////////////////////////////////////////////////////
  //
  // start main user C program
  //
  /////////////////////////////////////////////////////////////////////////////
  initial
  begin : main_PROC
    exp_err=0;
    sys_cfg_done=0;
    host_done =0;
    host_ok=0;

    // wait for end of reset
    repeat (10) @(posedge clk);
    wait(rst_a === 1'b0);
    //wait for other blocks(accelerator) end of reset
    repeat (20) @(posedge clk);
    // start main program
    host_exec();
  end : main_PROC


endmodule
