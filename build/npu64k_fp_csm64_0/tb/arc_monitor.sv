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

`include "npu_tb_pkg.sv"

module arc_monitor
#(
    parameter string trace_file = "arc.trc"
)
(
    input [31:0]   wa_pc,
    input          commit_evt,
    input          excpn_evt,
    input [31:0]   aux_eret,
    input [31:0]   aux_ecr,
    input          irq_evt,
    input [7:0]    irq_num,
    input          sys_sleep_r,
    input [2:0]    sys_sleep_mode_r,
    input          sys_halt_r,
    input [31:0]   cycle,
    input          clk,
    input          rst_a
);

reg mon_en;
reg sys_sleep_r_d1, sys_halt_r_d1;

always @(posedge clk) begin
    sys_sleep_r_d1 <= sys_sleep_r;
    sys_halt_r_d1  <= sys_halt_r;
end

initial
begin
    mon_en = get_value_from_plusargs("SIM_MON_EN");

    if(mon_en) begin
        int fid = $fopen(trace_file, "w");
        forever begin
            @(negedge clk);

            if(commit_evt)
                $fwrite(fid, "@cycle=%0d: <INST commit> PC <= 0x%08x\n", cycle, wa_pc );

            if(excpn_evt) begin
                @(negedge clk);
                $fwrite(fid, "@cycle=%0d: <EXCPN taken> ERET <= 0x%08x, ECR <= 0x%08x\n", cycle, aux_eret, aux_ecr);
            end

            if(irq_evt)
                $fwrite(fid, "@cycle=%0d: <IRQ taken> ack IRQ(0x%08x)\n", cycle, irq_num);

            if(!sys_sleep_r_d1 & sys_sleep_r)
                $fwrite(fid, "--- cycle=%0d : core enters sleep(%0d) ---\n", cycle, sys_sleep_mode_r);
            if(sys_sleep_r_d1 & !sys_sleep_r)
                $fwrite(fid, "--- cycle=%0d : core exits sleep ---\n", cycle);

            if(!sys_halt_r_d1 & sys_halt_r)
                $fwrite(fid, "=== cycle=%0d : core enters halt ===\n", cycle);
            if(sys_halt_r_d1 & !sys_halt_r)
                $fwrite(fid, "=== cycle=%0d : core exits halt ===\n", cycle);

        end
        $fclose(fid);
    end
end


endmodule
