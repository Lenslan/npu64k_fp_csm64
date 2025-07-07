/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

`include "tb_defines.sv"
`include "npu_tb_pkg.sv"

module sim_terminator(
   input [31:0]  cycle,
   input         clk,
   input         rst_a
);

    reg run_host;
    reg run_l2_arc;
    reg run_l2_arc1;
    reg run_l1_all;
    reg run_slc0_arc;
    reg run_slc1_arc;
    reg run_slc2_arc;
    reg run_slc3_arc;
    reg run_slc4_arc;
    reg run_slc5_arc;
    reg run_slc6_arc;
    reg run_slc7_arc;
    reg run_slc8_arc;
    reg run_slc9_arc;
    reg run_slc10_arc;
    reg run_slc11_arc;
    reg run_slc12_arc;
    reg run_slc13_arc;
    reg run_slc14_arc;
    reg run_slc15_arc;

    wire host_ok = `TB_HOST.host_done & `TB_HOST.host_ok;
    wire host_ko = `TB_HOST.host_done & ~`TB_HOST.host_ok;
    wire l2arc_ko = run_l2_arc && `NPU_TOP.nl2arc0_sys_sleep_r && (`NPU_TOP.nl2arc0_sys_sleep_mode_r  == 'h6 );
    wire l2arc_ok = run_l2_arc ? `NPU_TOP.nl2arc0_sys_sleep_r && (`NPU_TOP.nl2arc0_sys_sleep_mode_r  == 'h7 ) : 1;
    wire l2arc1_ko = run_l2_arc1 && `NPU_TOP.nl2arc1_sys_sleep_r && (`NPU_TOP.nl2arc1_sys_sleep_mode_r  == 'h6 );
    wire l2arc1_ok = run_l2_arc1 ? `NPU_TOP.nl2arc1_sys_sleep_r && (`NPU_TOP.nl2arc1_sys_sleep_mode_r  == 'h7 ) : 1;
    //slice 0
    wire slc0_ko = run_slc0_arc && `NPU_TOP.sl0nl1arc_sys_sleep_r && (`NPU_TOP.sl0nl1arc_sys_sleep_mode_r == 'h6);
    wire slc0_ok = run_slc0_arc ?  `NPU_TOP.sl0nl1arc_sys_sleep_r && (`NPU_TOP.sl0nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 1
    wire slc1_ko = run_slc1_arc && `NPU_TOP.sl1nl1arc_sys_sleep_r && (`NPU_TOP.sl1nl1arc_sys_sleep_mode_r == 'h6);
    wire slc1_ok = run_slc1_arc ?  `NPU_TOP.sl1nl1arc_sys_sleep_r && (`NPU_TOP.sl1nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 2
    wire slc2_ko = run_slc2_arc && `NPU_TOP.sl2nl1arc_sys_sleep_r && (`NPU_TOP.sl2nl1arc_sys_sleep_mode_r == 'h6);
    wire slc2_ok = run_slc2_arc ?  `NPU_TOP.sl2nl1arc_sys_sleep_r && (`NPU_TOP.sl2nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 3
    wire slc3_ko = run_slc3_arc && `NPU_TOP.sl3nl1arc_sys_sleep_r && (`NPU_TOP.sl3nl1arc_sys_sleep_mode_r == 'h6);
    wire slc3_ok = run_slc3_arc ?  `NPU_TOP.sl3nl1arc_sys_sleep_r && (`NPU_TOP.sl3nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 4
    wire slc4_ko = run_slc4_arc && `NPU_TOP.sl4nl1arc_sys_sleep_r && (`NPU_TOP.sl4nl1arc_sys_sleep_mode_r == 'h6);
    wire slc4_ok = run_slc4_arc ?  `NPU_TOP.sl4nl1arc_sys_sleep_r && (`NPU_TOP.sl4nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 5
    wire slc5_ko = run_slc5_arc && `NPU_TOP.sl5nl1arc_sys_sleep_r && (`NPU_TOP.sl5nl1arc_sys_sleep_mode_r == 'h6);
    wire slc5_ok = run_slc5_arc ?  `NPU_TOP.sl5nl1arc_sys_sleep_r && (`NPU_TOP.sl5nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 6
    wire slc6_ko = run_slc6_arc && `NPU_TOP.sl6nl1arc_sys_sleep_r && (`NPU_TOP.sl6nl1arc_sys_sleep_mode_r == 'h6);
    wire slc6_ok = run_slc6_arc ?  `NPU_TOP.sl6nl1arc_sys_sleep_r && (`NPU_TOP.sl6nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 7
    wire slc7_ko = run_slc7_arc && `NPU_TOP.sl7nl1arc_sys_sleep_r && (`NPU_TOP.sl7nl1arc_sys_sleep_mode_r == 'h6);
    wire slc7_ok = run_slc7_arc ?  `NPU_TOP.sl7nl1arc_sys_sleep_r && (`NPU_TOP.sl7nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 8
    wire slc8_ko = run_slc8_arc && `NPU_TOP.sl8nl1arc_sys_sleep_r && (`NPU_TOP.sl8nl1arc_sys_sleep_mode_r == 'h6);
    wire slc8_ok = run_slc8_arc ?  `NPU_TOP.sl8nl1arc_sys_sleep_r && (`NPU_TOP.sl8nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 9
    wire slc9_ko = run_slc9_arc && `NPU_TOP.sl9nl1arc_sys_sleep_r && (`NPU_TOP.sl9nl1arc_sys_sleep_mode_r == 'h6);
    wire slc9_ok = run_slc9_arc ?  `NPU_TOP.sl9nl1arc_sys_sleep_r && (`NPU_TOP.sl9nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 10
    wire slc10_ko = run_slc10_arc && `NPU_TOP.sl10nl1arc_sys_sleep_r && (`NPU_TOP.sl10nl1arc_sys_sleep_mode_r == 'h6);
    wire slc10_ok = run_slc10_arc ?  `NPU_TOP.sl10nl1arc_sys_sleep_r && (`NPU_TOP.sl10nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 11
    wire slc11_ko = run_slc11_arc && `NPU_TOP.sl11nl1arc_sys_sleep_r && (`NPU_TOP.sl11nl1arc_sys_sleep_mode_r == 'h6);
    wire slc11_ok = run_slc11_arc ?  `NPU_TOP.sl11nl1arc_sys_sleep_r && (`NPU_TOP.sl11nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 12
    wire slc12_ko = run_slc12_arc && `NPU_TOP.sl12nl1arc_sys_sleep_r && (`NPU_TOP.sl12nl1arc_sys_sleep_mode_r == 'h6);
    wire slc12_ok = run_slc12_arc ?  `NPU_TOP.sl12nl1arc_sys_sleep_r && (`NPU_TOP.sl12nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 13
    wire slc13_ko = run_slc13_arc && `NPU_TOP.sl13nl1arc_sys_sleep_r && (`NPU_TOP.sl13nl1arc_sys_sleep_mode_r == 'h6);
    wire slc13_ok = run_slc13_arc ?  `NPU_TOP.sl13nl1arc_sys_sleep_r && (`NPU_TOP.sl13nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 14
    wire slc14_ko = run_slc14_arc && `NPU_TOP.sl14nl1arc_sys_sleep_r && (`NPU_TOP.sl14nl1arc_sys_sleep_mode_r == 'h6);
    wire slc14_ok = run_slc14_arc ?  `NPU_TOP.sl14nl1arc_sys_sleep_r && (`NPU_TOP.sl14nl1arc_sys_sleep_mode_r == 'h7) : 1;
    //slice 15
    wire slc15_ko = run_slc15_arc && `NPU_TOP.sl15nl1arc_sys_sleep_r && (`NPU_TOP.sl15nl1arc_sys_sleep_mode_r == 'h6);
    wire slc15_ok = run_slc15_arc ?  `NPU_TOP.sl15nl1arc_sys_sleep_r && (`NPU_TOP.sl15nl1arc_sys_sleep_mode_r == 'h7) : 1;


   wire test_ok =     l2arc_ok
                   && l2arc1_ok
                   && host_ok
                   && slc0_ok
                   && slc1_ok
                   && slc2_ok
                   && slc3_ok
                   && slc4_ok
                   && slc5_ok
                   && slc6_ok
                   && slc7_ok
                   && slc8_ok
                   && slc9_ok
                   && slc10_ok
                   && slc11_ok
                   && slc12_ok
                   && slc13_ok
                   && slc14_ok
                   && slc15_ok
                ;
   //
   wire test_ko =     l2arc_ko
                  ||  host_ko
                   || slc0_ko
                   || slc1_ko
                   || slc2_ko
                   || slc3_ko
                   || slc4_ko
                   || slc5_ko
                   || slc6_ko
                   || slc7_ko
                   || slc8_ko
                   || slc9_ko
                   || slc10_ko
                   || slc11_ko
                   || slc12_ko
                   || slc13_ko
                   || slc14_ko
                   || slc15_ko
                ;

//finish simulation
reg [31:0] max_cycle;
logic dis_kpi_clk;
initial
begin
    max_cycle = get_value_from_plusargs("MAX_CYCLE", 200000);
    dis_kpi_clk = get_value_from_plusargs("DIS_KPI_CLK", 0);
    if(!dis_kpi_clk) max_cycle = max_cycle * 10;

    run_host  = get_value_from_plusargs("RUN_HOST", `NPU_HAS_L2ARC);
    if ($test$plusargs("RUN_L2_ARC="))
        run_l2_arc = get_value_from_plusargs("RUN_L2_ARC",0);
    else
        run_l2_arc=0;
    run_l2_arc1 = get_value_from_plusargs("RUN_L2_ARC1",0);
    run_l1_all = get_value_from_plusargs("RUN_L1_ALL",0);
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
    assert(run_l2_arc
        || run_host
        || run_l2_arc1
        || run_slc0_arc
        || run_slc1_arc
        || run_slc2_arc
        || run_slc3_arc
        || run_slc4_arc
        || run_slc5_arc
        || run_slc6_arc
        || run_slc7_arc
        || run_slc8_arc
        || run_slc9_arc
        || run_slc10_arc
        || run_slc11_arc
        || run_slc12_arc
        || run_slc13_arc
        || run_slc14_arc
        || run_slc15_arc
    );

    forever
    begin
        @(posedge clk);
        if ( test_ok || test_ko || `TB_HOST.force_exit)
        begin // }
            $display("*******************************************************");
            if(run_host) begin
                if(host_ok)      $display("Host run successfully");
                else if(host_ko) $display("Host run with error(s)");
                else             $display("Host run not finished");
            end else begin
                $display("Host did not run");
            end
            if(run_l2_arc) begin
                if(l2arc_ok)      $display("L2 ARC run successfully");
                else if(l2arc_ko) $display("L2 ARC run with error(s)");
                else              $display("L2 ARC run not finished");
            end else begin
                $display("L2 ARC did not run");
            end
            if(run_l2_arc1) begin
                if (l2arc1_ok)      $display("L2 ARC1 run successfully");
                else if (l2arc1_ko) $display("L2 ARC1 run with error(s)");
                else                $display("L2 ARC1 run not finished");
            end
            if(run_slc0_arc) begin
                if (slc0_ok)      $display("Slice 0 ARC run successfully");
                else if (slc0_ko) $display("Slice 0 ARC run with error(s)");
                else                 $display("Slice 0 ARC run not finished");
            end else begin
                $display("Slice 0 L1 ARC did not run");
            end
            if(run_slc1_arc) begin
                if (slc1_ok)      $display("Slice 1 ARC run successfully");
                else if (slc1_ko) $display("Slice 1 ARC run with error(s)");
                else                 $display("Slice 1 ARC run not finished");
            end else begin
                $display("Slice 1 L1 ARC did not run");
            end
            if(run_slc2_arc) begin
                if (slc2_ok)      $display("Slice 2 ARC run successfully");
                else if (slc2_ko) $display("Slice 2 ARC run with error(s)");
                else                 $display("Slice 2 ARC run not finished");
            end else begin
                $display("Slice 2 L1 ARC did not run");
            end
            if(run_slc3_arc) begin
                if (slc3_ok)      $display("Slice 3 ARC run successfully");
                else if (slc3_ko) $display("Slice 3 ARC run with error(s)");
                else                 $display("Slice 3 ARC run not finished");
            end else begin
                $display("Slice 3 L1 ARC did not run");
            end
            if(run_slc4_arc) begin
                if (slc4_ok)      $display("Slice 4 ARC run successfully");
                else if (slc4_ko) $display("Slice 4 ARC run with error(s)");
                else                 $display("Slice 4 ARC run not finished");
            end else begin
                $display("Slice 4 L1 ARC did not run");
            end
            if(run_slc5_arc) begin
                if (slc5_ok)      $display("Slice 5 ARC run successfully");
                else if (slc5_ko) $display("Slice 5 ARC run with error(s)");
                else                 $display("Slice 5 ARC run not finished");
            end else begin
                $display("Slice 5 L1 ARC did not run");
            end
            if(run_slc6_arc) begin
                if (slc6_ok)      $display("Slice 6 ARC run successfully");
                else if (slc6_ko) $display("Slice 6 ARC run with error(s)");
                else                 $display("Slice 6 ARC run not finished");
            end else begin
                $display("Slice 6 L1 ARC did not run");
            end
            if(run_slc7_arc) begin
                if (slc7_ok)      $display("Slice 7 ARC run successfully");
                else if (slc7_ko) $display("Slice 7 ARC run with error(s)");
                else                 $display("Slice 7 ARC run not finished");
            end else begin
                $display("Slice 7 L1 ARC did not run");
            end
            if(run_slc8_arc) begin
                if (slc8_ok)      $display("Slice 8 ARC run successfully");
                else if (slc8_ko) $display("Slice 8 ARC run with error(s)");
                else                 $display("Slice 8 ARC run not finished");
            end else begin
                $display("Slice 8 L1 ARC did not run");
            end
            if(run_slc9_arc) begin
                if (slc9_ok)      $display("Slice 9 ARC run successfully");
                else if (slc9_ko) $display("Slice 9 ARC run with error(s)");
                else                 $display("Slice 9 ARC run not finished");
            end else begin
                $display("Slice 9 L1 ARC did not run");
            end
            if(run_slc10_arc) begin
                if (slc10_ok)      $display("Slice 10 ARC run successfully");
                else if (slc10_ko) $display("Slice 10 ARC run with error(s)");
                else                 $display("Slice 10 ARC run not finished");
            end else begin
                $display("Slice 10 L1 ARC did not run");
            end
            if(run_slc11_arc) begin
                if (slc11_ok)      $display("Slice 11 ARC run successfully");
                else if (slc11_ko) $display("Slice 11 ARC run with error(s)");
                else                 $display("Slice 11 ARC run not finished");
            end else begin
                $display("Slice 11 L1 ARC did not run");
            end
            if(run_slc12_arc) begin
                if (slc12_ok)      $display("Slice 12 ARC run successfully");
                else if (slc12_ko) $display("Slice 12 ARC run with error(s)");
                else                 $display("Slice 12 ARC run not finished");
            end else begin
                $display("Slice 12 L1 ARC did not run");
            end
            if(run_slc13_arc) begin
                if (slc13_ok)      $display("Slice 13 ARC run successfully");
                else if (slc13_ko) $display("Slice 13 ARC run with error(s)");
                else                 $display("Slice 13 ARC run not finished");
            end else begin
                $display("Slice 13 L1 ARC did not run");
            end
            if(run_slc14_arc) begin
                if (slc14_ok)      $display("Slice 14 ARC run successfully");
                else if (slc14_ko) $display("Slice 14 ARC run with error(s)");
                else                 $display("Slice 14 ARC run not finished");
            end else begin
                $display("Slice 14 L1 ARC did not run");
            end
            if(run_slc15_arc) begin
                if (slc15_ok)      $display("Slice 15 ARC run successfully");
                else if (slc15_ko) $display("Slice 15 ARC run with error(s)");
                else                 $display("Slice 15 ARC run not finished");
            end else begin
                $display("Slice 15 L1 ARC did not run");
            end
            if (test_ok) $display("sim_terminator: Test passed");
            if (test_ko) $display("sim_terminator: Test failed");
            $display("*******************************************************");
            $finish;
        end

        if(cycle==max_cycle) begin
            $display("*************************************************************************************");
            $display("Simulation terminated because it reached the max allowed cycle (%0d),", max_cycle);
            $display("*************************************************************************************");
            //force `L1_ARC.sim_terminate = 1;  //indicate the call that the simulation is going to be terminated
            repeat (10) @(posedge clk);
            $finish;
        end
    end
end

endmodule
