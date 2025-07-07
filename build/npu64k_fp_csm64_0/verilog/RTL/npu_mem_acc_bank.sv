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

// One bank of a NPU accumulator memory
// Select between different implementations
//   - behavioral model for simulation
//   - FGPA friendly model for prototyping
//   - SRAM macro for physical implementation

`include "npu_sram_defines.sv"

// Use ASIC memory macros by default when doing synthesis, but not on FPGA.
`ifdef SYNTHESIS  // enable FPGA or Synthesis model, otherwise use simulation behavior model
  `ifndef FPGA_INFER_MEMORIES  // FPGA RAM model
    `include "npu_defines.v"
    `define NPU_USE_ASIC_MEMORIES 1 // ASIC RAM model
  `endif
`endif

module npu_mem_acc_bank #(
    parameter int MEM_TARGET = 0,
    parameter int MEM_INDEX  = 0,
    parameter int ADDR_WIDTH = 10,
    parameter int DATA_WIDTH = 32,
    parameter int MASK_WIDTH = 32,
    parameter FILE_NAME  = "npu_mem_acc_bank.hex"
) (
    input  logic                   clk,
    input  logic                   mem_en,  // Memory enable (chip select)
    input  logic                   wr_en,   // Write enable (0:read, 1:write)
    input  logic [ADDR_WIDTH-1:0]  addr,    // Word address
    input  logic [DATA_WIDTH-1:0]  wr_data, // Write data
    input  logic [MASK_WIDTH-1:0]  wr_mask, // Write enable mask (strobe)
    output logic [DATA_WIDTH-1:0]  rd_data, // Read data
// spyglass disable_block W240
//SMD:Unread input
//SJ :ds sd and ls used in NPU_MEM_POWER_DOMAINS config
    input  logic                   ds,      // Deep sleep, active high
    input  logic                   sd,      // Shutdown, active high
    input  logic                   ls       // Light sleep, active high
// spyglass enable_block W240
);

    // Bit-level write-enable
    logic [DATA_WIDTH-1:0] bwe;

    // Sub Element Width
    localparam int SEW = DATA_WIDTH / MASK_WIDTH;
    generate
        genvar i;
        for (i=0; i<MASK_WIDTH; i=i+1) begin: gen_bwe
            assign bwe[SEW*(i+1)-1 : SEW*i] = {SEW{wr_mask[i]}};
        end
    endgenerate

    // Tie off light sleep
    logic i_ls;
    assign i_ls = 1'b0;

    `ifdef NPU_USE_ASIC_MEMORIES
    // Memory macro
    `Mem_npu_acc_bank u_npu_mem_acc_bank_macro (
        .ME(mem_en),
        .Q(rd_data),
        .D(wr_data),
        .ADR(addr),
        .WE(wr_en),
        .WEM(bwe),
      `ifdef NPU_MEM_POWER_DOMAINS
        .DS(ds),
        .SD(sd),
      `endif
        .LS(i_ls),
        .CLK(clk)
    );

    `elsif FPGA_INFER_MEMORIES
    // FPGA memory model
    npu_fpga_sp_ram  #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ELEM_WIDTH(SEW)
    ) u_npu_mem_acc_bank_model (
        .clk     (clk),
        .mem_en  (mem_en),
        .wr_en   (wr_en),
        .addr    (addr),
        .rd_data (rd_data),
        .wr_mask (wr_mask),
        .wr_data (wr_data)
    );

    `else
    // Behavioral simulation model
    npu_sp_sram #(
        .MEM_TARGET(MEM_TARGET),
        .MEM_INDEX (MEM_INDEX ),
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .FILE_NAME (FILE_NAME)
    ) u_npu_mem_acc_bank_model (
        .clk     (clk),
        .mem_en  (mem_en),
        .wr_en   (wr_en),
        .addr    (addr),
        .rd_data (rd_data),
        .bwe     (bwe),
        .wr_data (wr_data),
        .ds      (ds),
        .sd      (sd),
        .ls      (i_ls)
    );
    `endif

endmodule : npu_mem_acc_bank
