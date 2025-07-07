interface npu_clk_rst_intf();
  logic npu_l1_clk, npu_core_clk, cfg_axi_clk, noc_axi_clk, arcsync_clk, arcsync_axi_clk, debug_clk, wdt_clk;
  logic npu_l1_rst, npu_core_rst, cfg_axi_rst, noc_axi_rst, arcsync_rst, arcsync_axi_rst, debug_rst, wdt_rst;
endinterface

class clk_rst_pkt;
  int npu_l1_cr; //clock ratio bwtween l1 and npu_core
  int noc_axi_cr; //clock ratio bwtween noc and npu_core
  int cfg_axi_cr; //clock ratio bwtween cfg and npu_core
  int arcsync_axi_cr; //clock ratio bwtween arcsync axi and npu_core 
  int arcsync_cr; //clock ratio bwtween arcsync and npu_core
  int debug_cr; //clock ratio bwtween debu and npu_core
  int wdt_cr; //clock ratio bwtween wdt and npu_core

  virtual npu_clk_rst_intf vif;

  rand int npu_core_clk_period; //npu core clock period
  rand int tunit;               //unit of releative cycle 
  //clock period
  rand int npu_l1_clk_cycle;
  rand int npu_core_clk_cycle;
  rand int noc_axi_clk_cycle;
  rand int cfg_axi_clk_cycle;
  rand int arcsync_axi_clk_cycle;
  rand int arcsync_clk_cycle;
  rand int debug_clk_cycle;
  rand int wdt_clk_cycle;

  //reset period
  rand int npu_l1_rst_cycle;
  rand int npu_core_rst_cycle;
  rand int noc_axi_rst_cycle;
  rand int cfg_axi_rst_cycle;
  rand int arcsync_axi_rst_cycle;
  rand int arcsync_rst_cycle;
  rand int debug_rst_cycle;
  rand int wdt_rst_cycle;

  //clock delay
  rand int npu_l1_clk_dly;
  rand int npu_core_clk_dly;
  rand int cfg_axi_clk_dly;
  rand int noc_axi_clk_dly;
  rand int arcsync_clk_dly;
  rand int arcsync_axi_clk_dly;
  rand int debug_clk_dly;
  rand int wdt_clk_dly;

  //reset delay
  rand int npu_l1_rst_dly;
  rand int npu_core_rst_dly;
  rand int cfg_axi_rst_dly;
  rand int noc_axi_rst_dly;
  rand int arcsync_rst_dly;
  rand int arcsync_axi_rst_dly;
  rand int debug_rst_dly;
  rand int wdt_rst_dly;

  constraint clk_dly_c {
    npu_l1_clk_dly dist {0:= 30, [1:500]:= 70,   [500:1500]:= 20};
    npu_core_clk_dly dist  {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    cfg_axi_clk_dly dist {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    noc_axi_clk_dly dist {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    arcsync_clk_dly dist {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    arcsync_axi_clk_dly dist {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    debug_clk_dly dist {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    wdt_clk_dly dist {0:= 30, [1:500]:= 70,  [500:1500]:= 20 };
    
    //arcsync_clk_dly <= arcsync_axi_clk_dly; 
  }
  
  constraint rst_dly_c {
    npu_l1_rst_dly dist {0:= 30, [1:100]:= 0 };
    npu_core_rst_dly dist  {0:= 30, [1:100]:= 0 };
    cfg_axi_rst_dly dist {0:= 30, [1:100]:= 0 };
    noc_axi_rst_dly dist {0:= 30, [1:100]:= 0 };
    arcsync_rst_dly dist {0:= 30, [1:100]:= 0 };
    arcsync_axi_rst_dly dist {0:= 30, [1:100]:= 0 };
    debug_rst_dly dist {0:= 30, [1:100]:= 0 };
    wdt_rst_dly dist {0:= 30, [1:100]:= 0 };
  } 

  constraint clk_cycle_c {
    npu_core_clk_period  inside { [100:1000]}; //as ref clk period [100ps:1000ps]
    tunit == npu_core_clk_cycle*(1000/npu_core_clk_period);

    //npu core
    npu_core_clk_cycle  == 10 ; //as base integer cycle, it's relative cycle
    //L1 clk
    npu_l1_clk_cycle >= npu_core_clk_cycle/npu_l1_cr;
    npu_l1_clk_cycle <= npu_core_clk_cycle*npu_l1_cr;
    npu_l1_clk_cycle >= arcsync_clk_cycle/arcsync_cr;
    npu_l1_clk_cycle <= arcsync_clk_cycle*arcsync_cr;
    //cfg 
    cfg_axi_clk_cycle >= npu_core_clk_cycle/cfg_axi_cr;
    cfg_axi_clk_cycle <= npu_core_clk_cycle*cfg_axi_cr;
    //noc
    noc_axi_clk_cycle >= npu_core_clk_cycle/noc_axi_cr;
    noc_axi_clk_cycle <= npu_core_clk_cycle*noc_axi_cr;
    //arcsync axi
    arcsync_axi_clk_cycle >= npu_core_clk_cycle/arcsync_axi_cr;
    arcsync_axi_clk_cycle <= npu_core_clk_cycle*arcsync_axi_cr;
    //arcsync
    arcsync_clk_cycle >= npu_core_clk_cycle/arcsync_cr;
    arcsync_clk_cycle <= npu_core_clk_cycle*arcsync_cr;
    //debug
    debug_clk_cycle >= npu_core_clk_cycle*2;
    debug_clk_cycle <= npu_core_clk_cycle*debug_cr;
    //wdt
    wdt_clk_cycle >= npu_core_clk_cycle*2;
    wdt_clk_cycle <= npu_core_clk_cycle*wdt_cr; 
  }

  constraint rst_cycle_c {
    npu_l1_rst_cycle inside { [1*npu_l1_clk_cycle:20*npu_l1_clk_cycle] };
    npu_core_rst_cycle inside { [1*npu_core_clk_cycle:20*npu_core_clk_cycle] };
    cfg_axi_rst_cycle inside { [1*cfg_axi_clk_cycle:20*cfg_axi_clk_cycle] };
    noc_axi_rst_cycle inside { [1*noc_axi_clk_cycle:20*noc_axi_clk_cycle] };
    arcsync_rst_cycle inside { [1*arcsync_clk_cycle:20*arcsync_clk_cycle] };
    arcsync_axi_rst_cycle inside { [1*arcsync_axi_clk_cycle:20*arcsync_axi_clk_cycle] };
    debug_rst_cycle inside { [1*debug_clk_cycle:20*debug_clk_cycle] };
    wdt_rst_cycle inside { [1*wdt_clk_cycle:20*wdt_clk_cycle] };
 
    (arcsync_axi_rst_dly) <= (arcsync_rst_dly);
    (arcsync_axi_rst_cycle + arcsync_axi_rst_dly) >= (arcsync_rst_cycle + arcsync_rst_dly);

    //(npu_core_rst_dly) <= (arcsync_rst_dly);
    //(npu_core_rst_cycle + npu_core_rst_dly) >= (arcsync_rst_cycle + arcsync_rst_dly);    
  }

//====================
//  cover groups
//====================
covergroup clk_dly_c_covergroup;
  cov_npu_l1_clk_dly      : coverpoint npu_l1_clk_dly      { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_npu_core_clk_dly    : coverpoint npu_core_clk_dly    { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_cfg_axi_clk_dly     : coverpoint cfg_axi_clk_dly     { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_arcsync_clk_dly     : coverpoint arcsync_clk_dly     { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_noc_axi_clk_dly     : coverpoint noc_axi_clk_dly     { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_arcsync_axi_clk_dly : coverpoint arcsync_axi_clk_dly { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_debug_clk_dly       : coverpoint debug_clk_dly       { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
  cov_wdt_clk_dly         : coverpoint wdt_clk_dly         { bins min = {0}; bins mid[10] = {[1:500]}; bins max[10] = {[501 : 1500]};  }
endgroup

covergroup rst_dly_c_covergroup;
  cov_npu_l1_rst_dly      : coverpoint npu_l1_rst_dly      { bins delay_0 = {0}; }
  cov_npu_core_rst_dly    : coverpoint npu_core_rst_dly    { bins delay_0 = {0};  }
  cov_cfg_axi_rst_dly     : coverpoint cfg_axi_rst_dly     { bins delay_0 = {0};  }
  cov_noc_axi_rst_dly     : coverpoint noc_axi_rst_dly     { bins delay_0 = {0};  }
  cov_arcsync_rst_dly     : coverpoint arcsync_rst_dly     { bins delay_0 = {0};  }
  cov_arcsync_axi_rst_dly : coverpoint arcsync_axi_rst_dly { bins delay_0 = {0};  }
  cov_debug_rst_dly       : coverpoint debug_rst_dly       { bins delay_0 = {0};  }
  cov_wdt_rst_dly         : coverpoint wdt_rst_dly         { bins delay_0 = {0};  }
endgroup

covergroup clk_cycle_c_covergroup;
  cov_npu_core_clk_cycle    : coverpoint npu_core_clk_cycle    { bins referecn_cycle = {10}; }
  cov_npu_l1_clk_cycle      : coverpoint npu_l1_clk_cycle      { bins low[] = {[10/npu_l1_cr : 9]}; bins base = {10}; bins high[] = {[11 : 10*npu_l1_cr]};}
  cov_cfg_axi_clk_cycle     : coverpoint cfg_axi_clk_cycle     { bins low[] = {[10/cfg_axi_cr : 9]}; bins base = {10}; bins high[] = {[11 : 10*cfg_axi_cr]};}
  cov_noc_axi_clk_cycle     : coverpoint noc_axi_clk_cycle     { bins low[] = {[10/noc_axi_cr : 9]}; bins base = {10}; bins high[] = {[11 : 10*noc_axi_cr]};}
  cov_arcsync_axi_clk_cycle : coverpoint arcsync_axi_clk_cycle { bins low[] = {[10/arcsync_axi_cr : 9]}; bins base = {10}; bins high[] = {[11 : 10*arcsync_axi_cr]};}
  cov_arcsync_clk_cycle     : coverpoint arcsync_clk_cycle     { bins low[] = {[10/arcsync_cr : 9]}; bins base = {10}; bins high[] = {[11 : 10*arcsync_cr]};}
  cov_debug_clk_cycle       : coverpoint debug_clk_cycle       { bins low[] = {[10*2 : 10*debug_cr]};}
  cov_wdt_clk_cycle         : coverpoint wdt_clk_cycle         { bins low[] = {[10*2 : 10*wdt_cr]};}
endgroup

covergroup rst_cycle_c_covergroup;
  cov_npu_l1_rst_cycle      : coverpoint int'(npu_l1_rst_cycle/npu_l1_clk_cycle)           { bins rst_cycle[] = {[1:20]};}
  cov_npu_core_rst_cycle    : coverpoint int'(npu_core_rst_cycle/npu_core_clk_cycle)       { bins rst_cycle[] = {[1:20]};}
  cov_cfg_axi_rst_cycle     : coverpoint int'(cfg_axi_rst_cycle/cfg_axi_clk_cycle)         { bins rst_cycle[] = {[1:20]};}
  cov_noc_axi_rst_cycle     : coverpoint int'(noc_axi_rst_cycle/noc_axi_clk_cycle)         { bins rst_cycle[] = {[1:20]};}
  cov_arcsync_axi_rst_cycle : coverpoint int'(arcsync_axi_rst_cycle/arcsync_axi_clk_cycle) { bins rst_cycle[] = {[1:20]};}
  cov_arcsync_rst_cycle     : coverpoint int'(arcsync_rst_cycle/arcsync_clk_cycle)         { bins rst_cycle[] = {[1:20]};}
  cov_debug_rst_cycle       : coverpoint int'(debug_rst_cycle/debug_clk_cycle)             { bins rst_cycle[] = {[1:20]};}
  cov_wdt_rst_cycle         : coverpoint int'(wdt_rst_cycle/wdt_clk_cycle)                 { bins rst_cycle[] = {[1:20]};}
endgroup

  function new(input virtual npu_clk_rst_intf vif, int npu_l1_cr=2, int noc_axi_cr=3, int cfg_axi_cr=3, int arcsync_axi_cr=3 , int arcsync_cr=2, int debug_cr=5, int wdt_cr=10);
    this.vif = vif;
    this.npu_l1_cr  = npu_l1_cr;
    this.noc_axi_cr  = noc_axi_cr;
    this.cfg_axi_cr  = cfg_axi_cr;
    this.arcsync_axi_cr = arcsync_axi_cr;
    this.arcsync_cr  = arcsync_cr;
    this.debug_cr  = debug_cr;
    this.wdt_cr  = wdt_cr;
    this.clk_dly_c_covergroup = new();
    this.rst_dly_c_covergroup = new();
    this.clk_cycle_c_covergroup = new();
    this.rst_cycle_c_covergroup = new();
  endfunction

  function void sample ();
    this.clk_dly_c_covergroup.sample();
    this.rst_dly_c_covergroup.sample();
    this.clk_cycle_c_covergroup.sample();
    this.rst_cycle_c_covergroup.sample();
  endfunction

  function display_info();
    $display("###########################");
    $display("npu_l1_cre: %d", npu_l1_cr);
    $display("noc_axi_cr: %d", noc_axi_cr);
    $display("cfg_axi_cr: %d", cfg_axi_cr);
    $display("arcsync_axi_cr: %d", arcsync_axi_cr);
    $display("arcsync_cr: %d", arcsync_cr);
    $display("debug_cr: %d", debug_cr);
    $display("wdt_cr: %d", wdt_cr);
    $display("npu_core_clk_cycle : %d", npu_core_clk_cycle);
    $display("npu_l1_clk_cycle : %d", npu_l1_clk_cycle);
    $display("cfg_axi_clk_cycle : %d", cfg_axi_clk_cycle);
    $display("noc_axi_clk_cycle : %d", noc_axi_clk_cycle);
    $display("arcsync_clk_cycle : %d", arcsync_clk_cycle);
    $display("arcsync_axi_clk_cycle: %d", arcsync_axi_clk_cycle);
    $display("debug_clk_cycle: %d", debug_clk_cycle);
    $display("wdt_clk_cycle: %d", wdt_clk_cycle);
  endfunction: display_info

  task run();
    display_info();
    npu_clk_gen();
    npu_rst_gen();
    sample();
  endtask: run

  task npu_clk_gen();
    fork
      npu_l1_clk_gen();
      npu_core_clk_gen();
      cfg_axi_clk_gen();
      noc_axi_clk_gen();
      arcsync_axi_clk_gen();
      arcsync_clk_gen();
      debug_clk_gen();
      wdt_clk_gen();
    join_none
  endtask: npu_clk_gen
  
  task npu_rst_gen();
    fork
      npu_l1_rst_gen();
      npu_core_rst_gen();
      cfg_axi_rst_gen();
      noc_axi_rst_gen();
      arcsync_axi_rst_gen();
      arcsync_rst_gen();
      debug_rst_gen();
      wdt_rst_gen();
    join_none
  endtask: npu_rst_gen

  // 
  task npu_l1_clk_gen();
    vif.npu_l1_clk = 0;
    #(realtime'(npu_l1_clk_dly)/tunit);
    forever 
    begin
      vif.npu_l1_clk = 0;
      #(realtime'(npu_l1_clk_cycle)/(2*tunit));
      vif.npu_l1_clk = 1;
      #(realtime'(npu_l1_clk_cycle)/(2*tunit));
    end
  endtask: npu_l1_clk_gen
  // 
  task npu_core_clk_gen();
    vif.npu_core_clk = 0;
    #(realtime'(npu_core_clk_dly)/tunit);
    forever 
    begin
      vif.npu_core_clk = 0;
      #(realtime'(npu_core_clk_cycle)/(2*tunit));
      vif.npu_core_clk = 1;
      #(realtime'(npu_core_clk_cycle)/(2*tunit));
    end
  endtask: npu_core_clk_gen
  // 
  task cfg_axi_clk_gen();
    vif.cfg_axi_clk = 0;
    #(realtime'(cfg_axi_clk_dly)/tunit);
    forever 
    begin
      vif.cfg_axi_clk = 0;
      #(realtime'(cfg_axi_clk_cycle)/(2*tunit));
      vif.cfg_axi_clk = 1;
      #(realtime'(cfg_axi_clk_cycle)/(2*tunit));
    end
  endtask: cfg_axi_clk_gen  
  // 
  task noc_axi_clk_gen();
    vif.noc_axi_clk = 0;
    #(realtime'(noc_axi_clk_dly)/tunit);
    forever 
    begin
      vif.noc_axi_clk = 0;
      #(realtime'(noc_axi_clk_cycle)/(2*tunit));
      vif.noc_axi_clk = 1;
      #(realtime'(noc_axi_clk_cycle)/(2*tunit));
    end
  endtask: noc_axi_clk_gen
  // 
  task arcsync_axi_clk_gen();
    vif.arcsync_axi_clk = 0;
    #(realtime'(arcsync_axi_clk_dly)/tunit);
    forever 
    begin
      vif.arcsync_axi_clk = 0;
      #(realtime'(arcsync_axi_clk_cycle)/(2*tunit));
      vif.arcsync_axi_clk = 1;
      #(realtime'(arcsync_axi_clk_cycle)/(2*tunit));
    end
  endtask: arcsync_axi_clk_gen
  // 
  task arcsync_clk_gen();
    vif.arcsync_clk = 0;
    #(realtime'(arcsync_clk_dly)/tunit);
    forever 
    begin
      vif.arcsync_clk = 0;
      #(realtime'(arcsync_clk_cycle)/(2*tunit));
      vif.arcsync_clk = 1;
      #(realtime'(arcsync_clk_cycle)/(2*tunit));
    end
  endtask: arcsync_clk_gen
  // 
  task debug_clk_gen();
    vif.debug_clk = 0;
    #(realtime'(debug_clk_dly)/tunit);
    forever 
    begin
      vif.debug_clk = 0;
      #(realtime'(debug_clk_cycle)/(2*tunit));
      vif.debug_clk = 1;
      #(realtime'(debug_clk_cycle)/(2*tunit));
    end
  endtask: debug_clk_gen
  // 
  task wdt_clk_gen();
    vif.wdt_clk = 0;
    #(realtime'(wdt_clk_dly)/tunit);
    forever 
    begin
      vif.wdt_clk = 0;
      #(realtime'(wdt_clk_cycle)/(2*tunit));
      vif.wdt_clk = 1;
      #(realtime'(wdt_clk_cycle)/(2*tunit));
    end
  endtask: wdt_clk_gen

    // 
  task npu_l1_rst_gen();
    vif.npu_l1_rst = 0;
    #(realtime'(npu_l1_rst_dly)/tunit);
    vif.npu_l1_rst = 1;
    #(realtime'(npu_l1_rst_cycle)/tunit);
    vif.npu_l1_rst = 0;
  endtask: npu_l1_rst_gen
  // 
  task npu_core_rst_gen();
    vif.npu_core_rst = 0;
    #(realtime'(npu_core_rst_dly)/tunit);
    vif.npu_core_rst = 1;
    #(realtime'(npu_core_rst_cycle)/tunit);
    vif.npu_core_rst = 0;
  endtask: npu_core_rst_gen
  // 
  task cfg_axi_rst_gen();
    vif.cfg_axi_rst = 0;
    #(realtime'(cfg_axi_rst_dly)/tunit);
    vif.cfg_axi_rst = 1;
    #(realtime'(cfg_axi_rst_cycle)/tunit);
    vif.cfg_axi_rst = 0;
  endtask: cfg_axi_rst_gen  
  // 
  task noc_axi_rst_gen();
    vif.noc_axi_rst = 0;
    #(realtime'(noc_axi_rst_dly)/tunit);
    vif.noc_axi_rst = 1;
    #(realtime'(noc_axi_rst_cycle)/tunit);
    vif.noc_axi_rst = 0;
  endtask: noc_axi_rst_gen
  // 
  task arcsync_axi_rst_gen();
    vif.arcsync_axi_rst = 0;
    #(realtime'(arcsync_axi_rst_dly)/tunit);
    vif.arcsync_axi_rst = 1;
    #(realtime'(arcsync_axi_rst_cycle)/tunit);
    vif.arcsync_axi_rst = 0;
  endtask: arcsync_axi_rst_gen
  // 
  task arcsync_rst_gen();
    vif.arcsync_rst = 0;
    #(realtime'(arcsync_rst_dly)/tunit);
    vif.arcsync_rst = 1;
    #(realtime'(arcsync_rst_cycle)/tunit);
    vif.arcsync_rst = 0;
  endtask: arcsync_rst_gen
  // 
  task debug_rst_gen();
    vif.debug_rst = 0;
    #(realtime'(debug_rst_dly)/tunit);
    vif.debug_rst = 1;
    #(realtime'(debug_rst_cycle)/tunit);
    vif.debug_rst = 0;
  endtask: debug_rst_gen
  // 
  task wdt_rst_gen();
    vif.wdt_rst = 0;
    #(realtime'(wdt_rst_dly)/tunit);
    vif.wdt_rst = 1;
    #(realtime'(wdt_rst_cycle)/tunit);
    vif.wdt_rst = 0;
  endtask: wdt_rst_gen


endclass
