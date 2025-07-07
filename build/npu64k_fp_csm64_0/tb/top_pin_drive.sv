`include "npu_tb_pkg.sv"

module top_pin_drive(npu_tb_intf tb_if);

`define DRIVE_PIN(NAME, VALUE) \
    tb_if.NAME = get_hex_value_from_plusargs("NAME", VALUE);

  initial
  begin
    `DRIVE_PIN(npu_sys_csm_addr_base,    24'h00b000)
    `DRIVE_PIN(npu_sys_periph_addr_base, 24'h00d000)



    // npx
      // L2 arc
        `DRIVE_PIN(nl2arc0_ext_arc_halt_req_a,0)
        `DRIVE_PIN(nl2arc1_ext_arc_halt_req_a,0)

      // L1 arc
        `DRIVE_PIN(sl0nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl1nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl2nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl3nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl4nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl5nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl6nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl7nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl8nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl9nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl10nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl11nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl12nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl13nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl14nl1arc_ext_arc_halt_req_a,0)
        `DRIVE_PIN(sl15nl1arc_ext_arc_halt_req_a,0)









    `DRIVE_PIN(arcsync_core_iso_override, 0)
  end 
  


reg run_l2_arc, boot_l2_with_pin, halt_l2_with_pin;
reg trigger_nl2arc_irq0_a, trigger_nl2arc_irq1_a;
reg trigger_test_mode;
reg run_l1_all, boot_l1_with_pin, halt_l1_with_pin;
  reg run_slc0_arc, boot_slc0_with_pin, halt_slc0_with_pin;
  reg run_slc1_arc, boot_slc1_with_pin, halt_slc1_with_pin;
  reg run_slc2_arc, boot_slc2_with_pin, halt_slc2_with_pin;
  reg run_slc3_arc, boot_slc3_with_pin, halt_slc3_with_pin;
  reg run_slc4_arc, boot_slc4_with_pin, halt_slc4_with_pin;
  reg run_slc5_arc, boot_slc5_with_pin, halt_slc5_with_pin;
  reg run_slc6_arc, boot_slc6_with_pin, halt_slc6_with_pin;
  reg run_slc7_arc, boot_slc7_with_pin, halt_slc7_with_pin;
  reg run_slc8_arc, boot_slc8_with_pin, halt_slc8_with_pin;
  reg run_slc9_arc, boot_slc9_with_pin, halt_slc9_with_pin;
  reg run_slc10_arc, boot_slc10_with_pin, halt_slc10_with_pin;
  reg run_slc11_arc, boot_slc11_with_pin, halt_slc11_with_pin;
  reg run_slc12_arc, boot_slc12_with_pin, halt_slc12_with_pin;
  reg run_slc13_arc, boot_slc13_with_pin, halt_slc13_with_pin;
  reg run_slc14_arc, boot_slc14_with_pin, halt_slc14_with_pin;
  reg run_slc15_arc, boot_slc15_with_pin, halt_slc15_with_pin;
reg clk_enable_force, clk_enable_for_cov;

initial 
begin
    clk_enable_force = get_value_from_plusargs("EN_TB_FORCE_CLK_ENABLE", 0);
    clk_enable_for_cov = get_value_from_plusargs("EN_CLK_ENABLE_COV", 0);

    run_l2_arc            = get_value_from_plusargs("RUN_L2_ARC", 0);
    boot_l2_with_pin      = get_value_from_plusargs("BOOT_L2_WITH_PIN", 0);
	halt_l2_with_pin      = get_value_from_plusargs("HALT_L2_WITH_PIN", 0);
	trigger_nl2arc_irq0_a = get_value_from_plusargs("PIN_IRQ0_A",0);
	trigger_nl2arc_irq1_a = get_value_from_plusargs("PIN_IRQ1_A",0);
    trigger_test_mode     = get_value_from_plusargs("TEST_MODE",0);
    run_l1_all            = get_value_from_plusargs("RUN_L1_ALL", 0);
    boot_l1_with_pin      = get_value_from_plusargs("BOOT_L1_WITH_PIN", 0);
	halt_l1_with_pin      = get_value_from_plusargs("HALT_L1_WITH_PIN", 0);
    run_slc0_arc         = get_value_from_plusargs("RUN_SLC0_ARC", run_l1_all);
    boot_slc0_with_pin   = get_value_from_plusargs("BOOT_SLC0_WITH_PIN", boot_l1_with_pin);
	halt_slc0_with_pin   = get_value_from_plusargs("HALT_SLC0_WITH_PIN", halt_l1_with_pin);
    run_slc1_arc         = get_value_from_plusargs("RUN_SLC1_ARC", run_l1_all);
    boot_slc1_with_pin   = get_value_from_plusargs("BOOT_SLC1_WITH_PIN", boot_l1_with_pin);
	halt_slc1_with_pin   = get_value_from_plusargs("HALT_SLC1_WITH_PIN", halt_l1_with_pin);
    run_slc2_arc         = get_value_from_plusargs("RUN_SLC2_ARC", run_l1_all);
    boot_slc2_with_pin   = get_value_from_plusargs("BOOT_SLC2_WITH_PIN", boot_l1_with_pin);
	halt_slc2_with_pin   = get_value_from_plusargs("HALT_SLC2_WITH_PIN", halt_l1_with_pin);
    run_slc3_arc         = get_value_from_plusargs("RUN_SLC3_ARC", run_l1_all);
    boot_slc3_with_pin   = get_value_from_plusargs("BOOT_SLC3_WITH_PIN", boot_l1_with_pin);
	halt_slc3_with_pin   = get_value_from_plusargs("HALT_SLC3_WITH_PIN", halt_l1_with_pin);
    run_slc4_arc         = get_value_from_plusargs("RUN_SLC4_ARC", run_l1_all);
    boot_slc4_with_pin   = get_value_from_plusargs("BOOT_SLC4_WITH_PIN", boot_l1_with_pin);
	halt_slc4_with_pin   = get_value_from_plusargs("HALT_SLC4_WITH_PIN", halt_l1_with_pin);
    run_slc5_arc         = get_value_from_plusargs("RUN_SLC5_ARC", run_l1_all);
    boot_slc5_with_pin   = get_value_from_plusargs("BOOT_SLC5_WITH_PIN", boot_l1_with_pin);
	halt_slc5_with_pin   = get_value_from_plusargs("HALT_SLC5_WITH_PIN", halt_l1_with_pin);
    run_slc6_arc         = get_value_from_plusargs("RUN_SLC6_ARC", run_l1_all);
    boot_slc6_with_pin   = get_value_from_plusargs("BOOT_SLC6_WITH_PIN", boot_l1_with_pin);
	halt_slc6_with_pin   = get_value_from_plusargs("HALT_SLC6_WITH_PIN", halt_l1_with_pin);
    run_slc7_arc         = get_value_from_plusargs("RUN_SLC7_ARC", run_l1_all);
    boot_slc7_with_pin   = get_value_from_plusargs("BOOT_SLC7_WITH_PIN", boot_l1_with_pin);
	halt_slc7_with_pin   = get_value_from_plusargs("HALT_SLC7_WITH_PIN", halt_l1_with_pin);
    run_slc8_arc         = get_value_from_plusargs("RUN_SLC8_ARC", run_l1_all);
    boot_slc8_with_pin   = get_value_from_plusargs("BOOT_SLC8_WITH_PIN", boot_l1_with_pin);
	halt_slc8_with_pin   = get_value_from_plusargs("HALT_SLC8_WITH_PIN", halt_l1_with_pin);
    run_slc9_arc         = get_value_from_plusargs("RUN_SLC9_ARC", run_l1_all);
    boot_slc9_with_pin   = get_value_from_plusargs("BOOT_SLC9_WITH_PIN", boot_l1_with_pin);
	halt_slc9_with_pin   = get_value_from_plusargs("HALT_SLC9_WITH_PIN", halt_l1_with_pin);
    run_slc10_arc         = get_value_from_plusargs("RUN_SLC10_ARC", run_l1_all);
    boot_slc10_with_pin   = get_value_from_plusargs("BOOT_SLC10_WITH_PIN", boot_l1_with_pin);
	halt_slc10_with_pin   = get_value_from_plusargs("HALT_SLC10_WITH_PIN", halt_l1_with_pin);
    run_slc11_arc         = get_value_from_plusargs("RUN_SLC11_ARC", run_l1_all);
    boot_slc11_with_pin   = get_value_from_plusargs("BOOT_SLC11_WITH_PIN", boot_l1_with_pin);
	halt_slc11_with_pin   = get_value_from_plusargs("HALT_SLC11_WITH_PIN", halt_l1_with_pin);
    run_slc12_arc         = get_value_from_plusargs("RUN_SLC12_ARC", run_l1_all);
    boot_slc12_with_pin   = get_value_from_plusargs("BOOT_SLC12_WITH_PIN", boot_l1_with_pin);
	halt_slc12_with_pin   = get_value_from_plusargs("HALT_SLC12_WITH_PIN", halt_l1_with_pin);
    run_slc13_arc         = get_value_from_plusargs("RUN_SLC13_ARC", run_l1_all);
    boot_slc13_with_pin   = get_value_from_plusargs("BOOT_SLC13_WITH_PIN", boot_l1_with_pin);
	halt_slc13_with_pin   = get_value_from_plusargs("HALT_SLC13_WITH_PIN", halt_l1_with_pin);
    run_slc14_arc         = get_value_from_plusargs("RUN_SLC14_ARC", run_l1_all);
    boot_slc14_with_pin   = get_value_from_plusargs("BOOT_SLC14_WITH_PIN", boot_l1_with_pin);
	halt_slc14_with_pin   = get_value_from_plusargs("HALT_SLC14_WITH_PIN", halt_l1_with_pin);
    run_slc15_arc         = get_value_from_plusargs("RUN_SLC15_ARC", run_l1_all);
    boot_slc15_with_pin   = get_value_from_plusargs("BOOT_SLC15_WITH_PIN", boot_l1_with_pin);
	halt_slc15_with_pin   = get_value_from_plusargs("HALT_SLC15_WITH_PIN", halt_l1_with_pin);
   fork 
     if (clk_enable_force ==1) begin
		$display("enabled clk_en force mechanism in TB");
        clk_en_force();
     end
     config_csm_base();
     test_mode();
   join_none

`ifndef TB_MDB  //{ (`TB_MDB != 1
    @(posedge `TB_TOP.u_sim_terminator.host_ok);
`endif //}
	repeat(200) @(posedge `TB_TOP.npu_core_clk);
	halt_system_by_pin();
	repeat(100) @(posedge `TB_TOP.npu_core_clk);
    boot_system_by_pin();
	irq_pin();

end


task clk_en_force();
logic [3:0] rand_value_arc0;
logic [3:0] rand_value_arc1;
    logic [3:0] rand_value_slc0;
    logic [3:0] rand_value_slc1;
    logic [3:0] rand_value_slc2;
    logic [3:0] rand_value_slc3;
    logic [3:0] rand_value_slc4;
    logic [3:0] rand_value_slc5;
    logic [3:0] rand_value_slc6;
    logic [3:0] rand_value_slc7;
    logic [3:0] rand_value_slc8;
    logic [3:0] rand_value_slc9;
    logic [3:0] rand_value_slc10;
    logic [3:0] rand_value_slc11;
    logic [3:0] rand_value_slc12;
    logic [3:0] rand_value_slc13;
    logic [3:0] rand_value_slc14;
    logic [3:0] rand_value_slc15;
    logic [3:0] rand_value_grp0;
    logic [3:0] rand_value_grp1;
    logic [3:0] rand_value_grp2;
    logic [3:0] rand_value_grp3;

fork 
       begin
       while(1) begin
               rand_value_arc0 = $random%16;
    	       repeat(rand_value_arc0) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.nl2arc0_clk_en_a = 0;
    	       repeat(rand_value_arc0) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.nl2arc0_clk_en_a = 1;
       end
       end

       begin
       while(1) begin
               rand_value_arc1 = $random%16;
    	       repeat(rand_value_arc1) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.nl2arc1_clk_en_a = 0;
    	       repeat(rand_value_arc1) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.nl2arc1_clk_en_a = 1;
       end
       end   

       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_grp0 = $random%2;
    	       repeat(rand_value_grp0) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp0_clk_en_a = 0;
    	       repeat(rand_value_grp0) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp0_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_grp1 = $random%2;
    	       repeat(rand_value_grp1) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp1_clk_en_a = 0;
    	       repeat(rand_value_grp1) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp1_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_grp2 = $random%2;
    	       repeat(rand_value_grp2) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp2_clk_en_a = 0;
    	       repeat(rand_value_grp2) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp2_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_grp3 = $random%2;
    	       repeat(rand_value_grp3) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp3_clk_en_a = 0;
    	       repeat(rand_value_grp3) @ (posedge `NPU_TOP.npu_core_clk);
    	       force `NPU_TOP.grp3_clk_en_a = 1;
		   end
       end
       end 

       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc0 = $random%2;
    	       repeat(rand_value_slc0) @ (posedge `NPU_TOP.sl0_clk);
    	       force `NPU_TOP.sl0_clk_en_a = 0;
    	       repeat(rand_value_slc0) @ (posedge `NPU_TOP.sl0_clk);
    	       force `NPU_TOP.sl0_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc1 = $random%2;
    	       repeat(rand_value_slc1) @ (posedge `NPU_TOP.sl1_clk);
    	       force `NPU_TOP.sl1_clk_en_a = 0;
    	       repeat(rand_value_slc1) @ (posedge `NPU_TOP.sl1_clk);
    	       force `NPU_TOP.sl1_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc2 = $random%2;
    	       repeat(rand_value_slc2) @ (posedge `NPU_TOP.sl2_clk);
    	       force `NPU_TOP.sl2_clk_en_a = 0;
    	       repeat(rand_value_slc2) @ (posedge `NPU_TOP.sl2_clk);
    	       force `NPU_TOP.sl2_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc3 = $random%2;
    	       repeat(rand_value_slc3) @ (posedge `NPU_TOP.sl3_clk);
    	       force `NPU_TOP.sl3_clk_en_a = 0;
    	       repeat(rand_value_slc3) @ (posedge `NPU_TOP.sl3_clk);
    	       force `NPU_TOP.sl3_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc4 = $random%2;
    	       repeat(rand_value_slc4) @ (posedge `NPU_TOP.sl4_clk);
    	       force `NPU_TOP.sl4_clk_en_a = 0;
    	       repeat(rand_value_slc4) @ (posedge `NPU_TOP.sl4_clk);
    	       force `NPU_TOP.sl4_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc5 = $random%2;
    	       repeat(rand_value_slc5) @ (posedge `NPU_TOP.sl5_clk);
    	       force `NPU_TOP.sl5_clk_en_a = 0;
    	       repeat(rand_value_slc5) @ (posedge `NPU_TOP.sl5_clk);
    	       force `NPU_TOP.sl5_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc6 = $random%2;
    	       repeat(rand_value_slc6) @ (posedge `NPU_TOP.sl6_clk);
    	       force `NPU_TOP.sl6_clk_en_a = 0;
    	       repeat(rand_value_slc6) @ (posedge `NPU_TOP.sl6_clk);
    	       force `NPU_TOP.sl6_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc7 = $random%2;
    	       repeat(rand_value_slc7) @ (posedge `NPU_TOP.sl7_clk);
    	       force `NPU_TOP.sl7_clk_en_a = 0;
    	       repeat(rand_value_slc7) @ (posedge `NPU_TOP.sl7_clk);
    	       force `NPU_TOP.sl7_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc8 = $random%2;
    	       repeat(rand_value_slc8) @ (posedge `NPU_TOP.sl8_clk);
    	       force `NPU_TOP.sl8_clk_en_a = 0;
    	       repeat(rand_value_slc8) @ (posedge `NPU_TOP.sl8_clk);
    	       force `NPU_TOP.sl8_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc9 = $random%2;
    	       repeat(rand_value_slc9) @ (posedge `NPU_TOP.sl9_clk);
    	       force `NPU_TOP.sl9_clk_en_a = 0;
    	       repeat(rand_value_slc9) @ (posedge `NPU_TOP.sl9_clk);
    	       force `NPU_TOP.sl9_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc10 = $random%2;
    	       repeat(rand_value_slc10) @ (posedge `NPU_TOP.sl10_clk);
    	       force `NPU_TOP.sl10_clk_en_a = 0;
    	       repeat(rand_value_slc10) @ (posedge `NPU_TOP.sl10_clk);
    	       force `NPU_TOP.sl10_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc11 = $random%2;
    	       repeat(rand_value_slc11) @ (posedge `NPU_TOP.sl11_clk);
    	       force `NPU_TOP.sl11_clk_en_a = 0;
    	       repeat(rand_value_slc11) @ (posedge `NPU_TOP.sl11_clk);
    	       force `NPU_TOP.sl11_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc12 = $random%2;
    	       repeat(rand_value_slc12) @ (posedge `NPU_TOP.sl12_clk);
    	       force `NPU_TOP.sl12_clk_en_a = 0;
    	       repeat(rand_value_slc12) @ (posedge `NPU_TOP.sl12_clk);
    	       force `NPU_TOP.sl12_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc13 = $random%2;
    	       repeat(rand_value_slc13) @ (posedge `NPU_TOP.sl13_clk);
    	       force `NPU_TOP.sl13_clk_en_a = 0;
    	       repeat(rand_value_slc13) @ (posedge `NPU_TOP.sl13_clk);
    	       force `NPU_TOP.sl13_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc14 = $random%2;
    	       repeat(rand_value_slc14) @ (posedge `NPU_TOP.sl14_clk);
    	       force `NPU_TOP.sl14_clk_en_a = 0;
    	       repeat(rand_value_slc14) @ (posedge `NPU_TOP.sl14_clk);
    	       force `NPU_TOP.sl14_clk_en_a = 1;
		   end
       end
       end 
       begin
       while(1) begin
		   if (clk_enable_for_cov) begin
			   //TO BE FILLED
           end else begin
               rand_value_slc15 = $random%2;
    	       repeat(rand_value_slc15) @ (posedge `NPU_TOP.sl15_clk);
    	       force `NPU_TOP.sl15_clk_en_a = 0;
    	       repeat(rand_value_slc15) @ (posedge `NPU_TOP.sl15_clk);
    	       force `NPU_TOP.sl15_clk_en_a = 1;
		   end
       end
       end 

join


endtask



task halt_system_by_pin();
    if(run_l2_arc) begin
		if(boot_l2_with_pin) begin
			force `TB_TOP.nl2arc0_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.nl2arc0_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.nl2arc0_ext_arc_halt_req_a;
            force `TB_TOP.nl2arc1_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.nl2arc1_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.nl2arc1_ext_arc_halt_req_a;
		end
	end

    if(run_slc0_arc) begin
		if(boot_slc0_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl0nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl0nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl0nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc1_arc) begin
		if(boot_slc1_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl1nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl1nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl1nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc2_arc) begin
		if(boot_slc2_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl2nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl2nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl2nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc3_arc) begin
		if(boot_slc3_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl3nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl3nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl3nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc4_arc) begin
		if(boot_slc4_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl4nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl4nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl4nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc5_arc) begin
		if(boot_slc5_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl5nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl5nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl5nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc6_arc) begin
		if(boot_slc6_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl6nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl6nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl6nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc7_arc) begin
		if(boot_slc7_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl7nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl7nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl7nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc8_arc) begin
		if(boot_slc8_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl8nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl8nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl8nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc9_arc) begin
		if(boot_slc9_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl9nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl9nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl9nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc10_arc) begin
		if(boot_slc10_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl10nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl10nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl10nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc11_arc) begin
		if(boot_slc11_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl11nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl11nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl11nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc12_arc) begin
		if(boot_slc12_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl12nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl12nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl12nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc13_arc) begin
		if(boot_slc13_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl13nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl13nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl13nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc14_arc) begin
		if(boot_slc14_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl14nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl14nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl14nl1arc_ext_arc_halt_req_a ;
		end
	end
    if(run_slc15_arc) begin
		if(boot_slc15_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl15nl1arc_ext_arc_halt_req_a = 1;
            @(posedge `TB_TOP.sl15nl1arc_ext_arc_halt_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl15nl1arc_ext_arc_halt_req_a ;
		end
	end
endtask:halt_system_by_pin

task boot_system_by_pin();
    if(run_l2_arc) begin
		if(boot_l2_with_pin) begin
			force `TB_TOP.nl2arc0_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.nl2arc0_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.nl2arc0_ext_arc_run_req_a;
            force `TB_TOP.nl2arc1_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.nl2arc1_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.nl2arc1_ext_arc_run_req_a;
		end
	end

    if(run_slc0_arc) begin
		if(boot_slc0_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl0nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl0nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl0nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc1_arc) begin
		if(boot_slc1_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl1nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl1nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl1nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc2_arc) begin
		if(boot_slc2_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl2nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl2nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl2nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc3_arc) begin
		if(boot_slc3_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl3nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl3nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl3nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc4_arc) begin
		if(boot_slc4_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl4nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl4nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl4nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc5_arc) begin
		if(boot_slc5_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl5nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl5nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl5nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc6_arc) begin
		if(boot_slc6_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl6nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl6nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl6nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc7_arc) begin
		if(boot_slc7_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl7nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl7nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl7nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc8_arc) begin
		if(boot_slc8_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl8nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl8nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl8nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc9_arc) begin
		if(boot_slc9_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl9nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl9nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl9nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc10_arc) begin
		if(boot_slc10_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl10nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl10nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl10nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc11_arc) begin
		if(boot_slc11_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl11nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl11nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl11nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc12_arc) begin
		if(boot_slc12_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl12nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl12nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl12nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc13_arc) begin
		if(boot_slc13_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl13nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl13nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl13nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc14_arc) begin
		if(boot_slc14_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl14nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl14nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl14nl1arc_ext_arc_run_req_a ;
		end
	end
    if(run_slc15_arc) begin
		if(boot_slc15_with_pin) begin
			repeat(1) @(posedge `TB_TOP.npu_core_clk);
            force `TB_TOP.sl15nl1arc_ext_arc_run_req_a = 1;
            @(posedge `TB_TOP.sl15nl1arc_ext_arc_run_ack);
            repeat(1) @(posedge `TB_TOP.npu_core_clk);
            release `TB_TOP.sl15nl1arc_ext_arc_run_req_a ;
		end
	end
endtask:boot_system_by_pin

task irq_pin();
    repeat(1) @(posedge `TB_TOP.npu_core_clk);
    if(trigger_nl2arc_irq0_a) begin
        force `TB_TOP.nl2arc_irq0_a = 1;
  	  fork
  	      @ (posedge `L2_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
  		  @ (posedge `L2_1_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
  	  join
  	  force `TB_TOP.nl2arc_irq0_a = 0;
    end
    repeat(200) @(posedge `TB_TOP.npu_core_clk);
    if(trigger_nl2arc_irq1_a) begin
        force `TB_TOP.nl2arc_irq1_a = 1;
  	  fork
  	      @ (posedge `L2_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
  		  @ (posedge `L2_1_ALB_CPU.u_alb_pd1.u_alb_core.u_alb_exu.u_alb_exec_pipe.irq_ack);
  	  join
  	  force `TB_TOP.nl2arc_irq1_a = 0;
    end
endtask: irq_pin

task test_mode();
    repeat(1) @(posedge `TB_TOP.npu_core_clk);
    if(trigger_test_mode) begin
        force `TB_TOP.test_mode = 1;
        repeat(100) @(posedge `TB_TOP.npu_core_clk);
        force `NPU_SL0.rst_a = 1;
        repeat(100) @(posedge `TB_TOP.npu_core_clk);
        force `NPU_SL0.rst_a = 0;
        repeat(2000) @(posedge `TB_TOP.npu_core_clk);
        force `TB_TOP.test_mode = 0;
    end
endtask:test_mode

task config_csm_base();
    tb_if.npu_csm_base = '0;
    repeat(1) @(posedge `TB_TOP.npu_core_clk);
    tb_if.npu_csm_base = '1;
    repeat(1) @(posedge `TB_TOP.npu_core_clk);
    tb_if.npu_csm_base = '0;
    repeat(1) @(posedge `TB_TOP.npu_core_clk);
    tb_if.npu_csm_base = get_hex_value_from_plusargs("NPU_CSM_BASE", 'he8);
endtask: config_csm_base

endmodule
