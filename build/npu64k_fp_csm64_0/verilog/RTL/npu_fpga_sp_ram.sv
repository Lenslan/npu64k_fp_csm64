/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
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

// Synchronous RAM, single port, bit-write enable
//
// NOTE: This module is meant for a FPGA target where appropriate RAMs will
//       be inferred by the FPGA synthesis tool. It is not meant for an ASIC
//       implementation.
//
module npu_fpga_sp_ram #(
    parameter integer ADDR_WIDTH = 16,
    parameter integer DATA_WIDTH = 64, // Size of one word
    parameter integer ELEM_WIDTH =  8  // Sub-elements width for write mask
) (
    input  wire                             clk,
    input  wire                             mem_en,  // Memory enable (chip select)
    input  wire                             wr_en,   // Write enable
    input  wire [ADDR_WIDTH-1:0]            addr,    // Word address
    input  wire [DATA_WIDTH-1:0]            wr_data,
    input  wire [DATA_WIDTH/ELEM_WIDTH-1:0] wr_mask,
    output  reg [DATA_WIDTH-1:0]            rd_data
);

    localparam [31:0] MEM_SIZE = 32'd1 << ADDR_WIDTH; // In number of words

    reg [DATA_WIDTH-1:0] mem[0:MEM_SIZE-1] /* synthesis syn_ramstyle = "block_ram,no_rw_check" */;

    always @(posedge clk)
    begin: PROC_mem_read
        if (mem_en)
            rd_data <= mem[addr];
    end

    genvar bk; // per bank
    generate
    for (bk = 0; bk < DATA_WIDTH/ELEM_WIDTH; bk = bk+1)
    begin: membank
        always @(posedge clk)
        begin: PROC_mem_write
            if (mem_en & wr_en & wr_mask[bk])
                mem[addr][ELEM_WIDTH*bk+:ELEM_WIDTH] <= wr_data[ELEM_WIDTH*bk+:ELEM_WIDTH];
        end
    end
    endgenerate

`ifndef SYNTHESIS // {

    initial
    begin: PROC_init
        mem_init();
        rd_data = mem[0];
    end

    localparam integer NUM_D32 = (DATA_WIDTH + 31) / 32;
    localparam integer D32_BW  = NUM_D32 * 32;

    task mem_init;
        begin : init_mem_content
            integer i, t;
            reg [D32_BW-1:0] tmp32;
        `ifdef EVCNN_RANDOM_MEMORIES
            //$display("%m (%0t): Initializing memory to random values",$time);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                for (t=0; t<NUM_D32; t=t+1) begin
                   tmp32[t*32 +: 32] = {$random};
                end
                mem[i] = tmp32[DATA_WIDTH-1:0];
            end
        `elsif EVCNN_CORRUPT_MEMORIES
            //$display("%m (%0t): Corrupting memory to X",$time);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                mem[i] = {DATA_WIDTH{1'bx}};
            end
        `elsif  EVCNN_POISON_MEMORIES
            tmp32 = {NUM_D32{32'hBADC0FFE}};
            //$display("%m (%0t): Initializing memory to %h",$time,tmp32[DATA_WIDTH-1:0]);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                mem[i] = tmp32[DATA_WIDTH-1:0];
            end
        `else // EVCNN_ZEROED_MEMORIES
            //$display("%m (%0t): Initializing memory to zero",$time);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                mem[i] = 0;
            end
        `endif
        end
    endtask

`endif // } SYNTHESIS

endmodule : npu_fpga_sp_ram
