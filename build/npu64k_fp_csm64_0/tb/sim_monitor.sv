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


module sim_monitor
#(parameter logic [31:0] TB_SIM_MON_EN='hffffffff)
(
   input [31:0]  cycle,
   input         l1_clk, 
   input         l2_clk,
   input         rst_a
);

  generate
    begin: arc_monitor0
    if (TB_SIM_MON_EN[0+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl0_arc.trc") 
      ) i_slc0_mon
      (
          .wa_pc({`SL0_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL0_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL0_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL0_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL0_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL0_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL0_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL0_ARC.sys_halt_r)
        , .sys_sleep_r(`SL0_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL0_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL0_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor1
    if (TB_SIM_MON_EN[1+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl1_arc.trc") 
      ) i_slc1_mon
      (
          .wa_pc({`SL1_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL1_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL1_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL1_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL1_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL1_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL1_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL1_ARC.sys_halt_r)
        , .sys_sleep_r(`SL1_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL1_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL1_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor2
    if (TB_SIM_MON_EN[2+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl2_arc.trc") 
      ) i_slc2_mon
      (
          .wa_pc({`SL2_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL2_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL2_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL2_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL2_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL2_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL2_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL2_ARC.sys_halt_r)
        , .sys_sleep_r(`SL2_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL2_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL2_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor3
    if (TB_SIM_MON_EN[3+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl3_arc.trc") 
      ) i_slc3_mon
      (
          .wa_pc({`SL3_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL3_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL3_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL3_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL3_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL3_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL3_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL3_ARC.sys_halt_r)
        , .sys_sleep_r(`SL3_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL3_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL3_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor4
    if (TB_SIM_MON_EN[4+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl4_arc.trc") 
      ) i_slc4_mon
      (
          .wa_pc({`SL4_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL4_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL4_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL4_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL4_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL4_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL4_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL4_ARC.sys_halt_r)
        , .sys_sleep_r(`SL4_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL4_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL4_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor5
    if (TB_SIM_MON_EN[5+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl5_arc.trc") 
      ) i_slc5_mon
      (
          .wa_pc({`SL5_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL5_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL5_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL5_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL5_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL5_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL5_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL5_ARC.sys_halt_r)
        , .sys_sleep_r(`SL5_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL5_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL5_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor6
    if (TB_SIM_MON_EN[6+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl6_arc.trc") 
      ) i_slc6_mon
      (
          .wa_pc({`SL6_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL6_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL6_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL6_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL6_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL6_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL6_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL6_ARC.sys_halt_r)
        , .sys_sleep_r(`SL6_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL6_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL6_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor7
    if (TB_SIM_MON_EN[7+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl7_arc.trc") 
      ) i_slc7_mon
      (
          .wa_pc({`SL7_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL7_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL7_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL7_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL7_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL7_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL7_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL7_ARC.sys_halt_r)
        , .sys_sleep_r(`SL7_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL7_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL7_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor8
    if (TB_SIM_MON_EN[8+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl8_arc.trc") 
      ) i_slc8_mon
      (
          .wa_pc({`SL8_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL8_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL8_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL8_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL8_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL8_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL8_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL8_ARC.sys_halt_r)
        , .sys_sleep_r(`SL8_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL8_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL8_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor9
    if (TB_SIM_MON_EN[9+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl9_arc.trc") 
      ) i_slc9_mon
      (
          .wa_pc({`SL9_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL9_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL9_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL9_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL9_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL9_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL9_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL9_ARC.sys_halt_r)
        , .sys_sleep_r(`SL9_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL9_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL9_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor10
    if (TB_SIM_MON_EN[10+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl10_arc.trc") 
      ) i_slc10_mon
      (
          .wa_pc({`SL10_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL10_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL10_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL10_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL10_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL10_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL10_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL10_ARC.sys_halt_r)
        , .sys_sleep_r(`SL10_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL10_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL10_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor11
    if (TB_SIM_MON_EN[11+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl11_arc.trc") 
      ) i_slc11_mon
      (
          .wa_pc({`SL11_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL11_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL11_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL11_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL11_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL11_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL11_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL11_ARC.sys_halt_r)
        , .sys_sleep_r(`SL11_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL11_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL11_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor12
    if (TB_SIM_MON_EN[12+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl12_arc.trc") 
      ) i_slc12_mon
      (
          .wa_pc({`SL12_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL12_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL12_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL12_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL12_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL12_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL12_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL12_ARC.sys_halt_r)
        , .sys_sleep_r(`SL12_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL12_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL12_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor13
    if (TB_SIM_MON_EN[13+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl13_arc.trc") 
      ) i_slc13_mon
      (
          .wa_pc({`SL13_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL13_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL13_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL13_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL13_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL13_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL13_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL13_ARC.sys_halt_r)
        , .sys_sleep_r(`SL13_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL13_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL13_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor14
    if (TB_SIM_MON_EN[14+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl14_arc.trc") 
      ) i_slc14_mon
      (
          .wa_pc({`SL14_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL14_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL14_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL14_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL14_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL14_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL14_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL14_ARC.sys_halt_r)
        , .sys_sleep_r(`SL14_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL14_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL14_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate
  generate
    begin: arc_monitor15
    if (TB_SIM_MON_EN[15+1])
      begin
      arc_monitor
      #(
          .trace_file("arc_logs/sl15_arc.trc") 
      ) i_slc15_mon
      (
          .wa_pc({`SL15_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`SL15_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`SL15_EXEC_EXCPN.take_excpn)
        , .aux_eret(`SL15_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`SL15_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`SL15_EXEC_EXCPN.irq_ack)
        , .irq_num(`SL15_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`SL15_ARC.sys_halt_r)
        , .sys_sleep_r(`SL15_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`SL15_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`SL15_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate

  generate
    begin: arc_monitor_l2arc
    if (TB_SIM_MON_EN[0])
      begin
      arc_monitor
      #( 
          .trace_file("arc_logs/l2_arc.trc") 
      ) i_l2arc_mon
      (
          .wa_pc({`L2_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`L2_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`L2_EXEC_EXCPN.take_excpn)
        , .aux_eret(`L2_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`L2_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`L2_EXEC_EXCPN.irq_ack)
        , .irq_num(`L2_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`L2_ARC.sys_halt_r)
        , .sys_sleep_r(`L2_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`L2_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`L2_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate

  generate
    begin: arc_monitor_l2arc1
    if (TB_SIM_MON_EN[`NPU_SLICE_NUM+1])
      begin
      arc_monitor
      #( 
          .trace_file("arc_logs/l2_arc1.trc") 
      ) i_l2arc1_mon
      (
          .wa_pc({`L2_1_EXEC_PIPE.wa_pc[31:1],1'b0})
        , .commit_evt(`L2_1_EXEC_CMT.ca_cmt_norm_evt)
        , .excpn_evt(`L2_1_EXEC_EXCPN.take_excpn)
        , .aux_eret(`L2_1_EXEC_EXCPN.ar_aux_eret_r)
        , .aux_ecr(`L2_1_EXEC_EXCPN.ar_aux_ecr_r)
        , .irq_evt(`L2_1_EXEC_EXCPN.irq_ack)
        , .irq_num(`L2_1_EXEC_EXCPN.irq_ack_num)
        , .sys_halt_r(`L2_1_ARC.sys_halt_r)
        , .sys_sleep_r(`L2_1_ARC.sys_sleep_r)
        , .sys_sleep_mode_r(`L2_1_ARC.sys_sleep_mode_r)
        , .cycle(cycle)
        , .clk(`L2_1_DPI_ARC.clk)
        , .rst_a(rst_a)
      );
      end
    end
  endgenerate




endmodule
