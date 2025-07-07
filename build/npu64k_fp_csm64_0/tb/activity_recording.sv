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

module activity_recording();

  // Activity recording for power flows
  int power_fsdb_en = 0;
  initial begin
    if ($value$plusargs("POWER_FSDB=%d", power_fsdb_en)) begin
        $display("POWER: Enabling power trigger detection");
    end
  end

  wire power_toggle; // detect power trigger in L2 or slice0, but not both
  assign power_toggle = 
                       ((`L2_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`L2_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`L2_EXU.db_active == 1'h0)) |
                        ((`L2_1_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`L2_1_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`L2_1_EXU.db_active == 1'h0)) |
                        ((`SL0_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL0_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL0_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL1_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL1_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL1_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL2_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL2_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL2_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL3_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL3_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL3_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL4_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL4_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL4_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL5_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL5_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL5_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL6_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL6_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL6_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL7_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL7_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL7_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL8_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL8_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL8_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL9_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL9_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL9_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL10_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL10_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL10_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL11_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL11_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL11_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL12_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL12_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL12_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL13_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL13_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL13_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL14_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL14_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL14_EXEC_PIPE.db_active == 1'h0)) |
                        ((`SL15_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_ren_r == 1'h1) &&
                         (`SL15_EXEC_PIPE.u_alb_aux_ctrl.aux_bcr_raddr_r[7:0] == 8'h60) &&
                         (`SL15_EXEC_PIPE.db_active == 1'h0)) |
                        1'b0;
  reg power_toggle_r = 0;

  `ifdef TB_VERDI
  always @(posedge power_toggle) begin
    if (power_fsdb_en != 0 && power_toggle !== 1'bx) begin
        if (power_toggle_r == 1'b0) begin
            $fsdbDumpfile("power.fsdb");
            if (power_fsdb_en == 1) begin
                $fsdbDumpvars(0, `ARCHIPELAGO, "+all");
            end else if (power_fsdb_en == 2) begin
                $fsdbDumpvars(0, `NPU_TOP.u_l1core0, "+all");
            end
            $display("POWER: Toggle Capture Started : time = ",$time);
        end else begin
            $fsdbDumpoff();
            $fsdbDumpFinish();
            $display("POWER: Toggle Capture Stopped : time = ",$time);
        end
        power_toggle_r <= ~power_toggle_r;
    end
  end
  `endif

endmodule
