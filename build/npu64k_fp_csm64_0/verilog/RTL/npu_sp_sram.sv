
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

/* ----------------------------------------------------------------------------
 * BEHAVIORAL MODEL
 * ----------------------------------------------------------------------------
 */

// Synchronous RAM, single port with bit-write enable,
// Read data output stays valid when mem_en is not asserted.
//
// NOTE: This module should not be synthesized, nor should it be used
//       for gate-level simulation as it contains no delay information.

// spyglass disable_block ALL
// SMD:
// SJ: This is a behavioral model and treated as a black box
`include "npu_sram_defines.sv"
module npu_sp_sram #(
    parameter int MEM_TARGET = 0,
    parameter int MEM_INDEX  = 0,
    parameter int ADDR_WIDTH = 16,
    parameter int DATA_WIDTH = 64,
    parameter FILE_NAME  = "npu_sp_sram.hex"  // Binary file used to initialize
) (
    input  wire                   clk,
    input  wire                   mem_en,  // Memory enable (chip select)
    input  wire                   wr_en,   // Write enable (0:read, 1:write)
    input  wire [ADDR_WIDTH-1:0]  addr,    // Word address
    input  wire [DATA_WIDTH-1:0]  wr_data,
    input  wire [DATA_WIDTH-1:0]  bwe,     // Bit-write enable mask
    input  wire                   ds,      // Deep sleep, active high
    input  wire                   sd,      // Shutdown, active high
    input  wire                   ls,      // Light sleep, active high
    output  reg [DATA_WIDTH-1:0]  rd_data
);

    localparam int NUM_D32 = (DATA_WIDTH + 31) / 32;
    localparam int D32_BW  = NUM_D32 * 32;
    localparam [31:0] MEM_SIZE = 32'd1 << ADDR_WIDTH; // In number of words

`ifndef SYNTHESIS   // {

    reg [D32_BW-1:0] t32;

    reg [DATA_WIDTH-1:0] mem[0:MEM_SIZE-1];

  `ifndef VERILATOR // {
    // Reset memory content when it transitions from shutdown (sd) to powered up (pu)
    reg  sd_dly;
    wire pu_rst_reload_mem = sd_dly && !sd;

    reg [DATA_WIDTH-1:0] mem_img[0:MEM_SIZE-1];

    always @(posedge clk)
    begin : mem_pu_PROC
       if (pu_rst_reload_mem)  begin
        int fd;

        mem_init();

        rd_data = mem[0];
        $display("%m: Due to powering up reset. Trying to load memory content from file %s", FILE_NAME);
        fd = $fopen(FILE_NAME, "r");
        if (fd != 0) begin
            $readmemh(FILE_NAME, mem);
            $fclose(fd);
        end

        for (int i=0; i<MEM_SIZE-1; i++) begin
            if (mem_img[i] != mem[i])
                $display("%m: powering up memory is different compare to memory image %s[%d]", FILE_NAME,i);
        end

       end
    end

    always @(posedge clk)
    begin: PROC_sd_delay
        sd_dly <= sd;
    end

    wire sd_erase = ((sd == 1'b1) & (sd_dly == 1'b0));
    wire unavail  = ((sd == 1'b1) | (ds == 1'b1));
  `endif // } VERILATOR

    always @(posedge clk)
    begin: PROC_mem
    `ifndef VERILATOR // {
        int  idx;
        if (sd_erase == 1'b1) begin
            // Erase the entire memory content when shutting down
            mem_init();
            rd_data <= {DATA_WIDTH{1'bx}};
        end
        else if (unavail == 1'b1) begin
            // Memory is in deep-sleep or shutdown mode (unavailable)
            // Ignore writes and return undefined read data
            rd_data <= {DATA_WIDTH{1'bx}};
        end
        else
    `endif // } VERILATOR
        if (mem_en) begin
            if (wr_en) begin
                mem[addr] <= (bwe & wr_data) | (~bwe & mem[addr]);
            end
            else begin
                rd_data <= mem[addr];
            end
        end
        else begin
          //restore to random data
          for (int t=0; t<NUM_D32; t=t+1) begin
              t32[t*32 +: 32] = {$random};
          end
          rd_data = t32[DATA_WIDTH-1:0];
        end
    end

    initial
    begin: PROC_init
        int fd;
        mem_init();
        $display("%m: Trying to load memory content from file %s", FILE_NAME);
        fd = $fopen(FILE_NAME, "r");
        if (fd != 0) begin
            $readmemh(FILE_NAME, mem);
            $fclose(fd);
        end

        $display("%m: Making a copy of memory image %s, to compare after power up", FILE_NAME);
        for (int i=0; i<MEM_SIZE-1; i++) begin
            mem_img[i] = mem[i];
        end

        rd_data = mem[0];
    `ifndef VERILATOR   // {
        sd_dly = 0;
    `endif              // }
    end

    task mem_init;
        begin : init_mem_content
            int i, t;
            reg [D32_BW-1:0] tmp32;
        `ifdef NPU_RANDOM_MEMORIES
            $display("%m (%0t): Initializing memory to random values",$time);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                for (t=0; t<NUM_D32; t=t+1) begin
                    tmp32[t*32 +: 32] = {$random};
                end
                mem[i] = tmp32[DATA_WIDTH-1:0];
            end
        `elsif NPU_CORRUPT_MEMORIES
            $display("%m (%0t): Corrupting memory to X",$time);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                mem[i] = {DATA_WIDTH{1'bx}};
            end
        `elsif NPU_ZEROED_MEMORIES
            $display("%m (%0t): Initializing memory to zero",$time);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                mem[i] = 0;
            end
        `else // NPU_POISON_MEMORIES
            tmp32 = {NUM_D32{32'hBADC0FFE}};
            $display("%m (%0t): Initializing memory to %h",$time,tmp32[DATA_WIDTH-1:0]);
            for (i=0; i<MEM_SIZE; i=i+1) begin
                mem[i] = tmp32[DATA_WIDTH-1:0];
            end
        `endif
            // Temporary disable ECC init
            //ecc_code_init();
        end
    endtask

    task setContent;
        // Ensure that there are only MEM_SIZE entries in the file!
        input [128*8:1] fname;
        int fd;
        begin
            $display("setContent: loading memory from file: %s", fname);
            fd = $fopen(fname, "r");
            if (fd != 0) begin
                $readmemh(fname, mem);
                $fclose(fd);
            end
        end
    endtask

/*
    // -- Initialize ECC codes
    //
    task ecc_code_init;
        begin:init_mem_ecc_code
            localparam UNUSED_D = 275 - DATA_WIDTH;
            int i;
            int j;

            reg [274:0]            org_data;
            reg [274:0]            flu_data;
            reg [ADDR_WIDTH-1:0]   address;

            reg [142:0]            fused_data;
            reg [8:0]              wm_ecc_code;

            for (i=0;i<MEM_SIZE; i=i+1) begin
                fused_data = 0;
                org_data = {{UNUSED_D{1'b0}},mem[i]};
                address  =  i;
                flu_data = org_data;

                if (MEM_TARGET == `NPU_MEM_TARGET_VM) begin
                    flu_data[53:48]   = vm_encoder(org_data[11         : 0         ]);
                    flu_data[59:54]   = vm_encoder(org_data[11 + 12 * 1: 0 + 12 * 1]);
                    flu_data[65:60]   = vm_encoder(org_data[11 + 12 * 2: 0 + 12 * 2]);
                    flu_data[71:66]   = vm_encoder(org_data[11 + 12 * 3: 0 + 12 * 3]);
                end
                if (MEM_TARGET == `NPU_MEM_TARGET_AM) begin
                    flu_data[136:128] = am_encoder(org_data[128*0+127:128*0+0]);
                end
                mem[i] = flu_data[DATA_WIDTH-1:0];
            end
        end
    endtask


    function [8:0] am_encoder;
        // Module input and output ports
        input [127:0] data_in;

        // The word which ECC will be calculated
        logic [127:0] word_in;
        // Hold generated EDC bits
        logic [7:0] edc_tmp;
        // Overall parity for Hammming SECDED code
        logic overall_parity;

        // Masks to select bits to be XORed
        localparam mask0 = 128'b10101010110101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010110101010101010110101011011;
        localparam mask1 = 128'b00110011011001100110011001100110011001100110011001100110011001100110011010011001100110011001100110011011001100110011011001101101;
        localparam mask2 = 128'b00111100011110000111100001111000011110000111100001111000011110000111100011100001111000011110000111100011110000111100011110001110;
        localparam mask3 = 128'b11000000011111111000000001111111100000000111111110000000011111111000000011111110000000011111111000000011111111000000011111110000;
        localparam mask4 = 128'b00000000011111111111111110000000000000000111111111111111100000000000000011111111111111100000000000000011111111111111100000000000;
        localparam mask5 = 128'b00000000011111111111111111111111111111111000000000000000000000000000000011111111111111111111111111111100000000000000000000000000;
        localparam mask6 = 128'b00000000011111111111111111111111111111111111111111111111111111111111111100000000000000000000000000000000000000000000000000000000;
        localparam mask7 = 128'b11111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;

        // Word to encode
        word_in = data_in;

        // To generate EDC bits, pick particular word bits by using masks, then XOR them
        edc_tmp[0] = ^(word_in & mask0);
        edc_tmp[1] = ^(word_in & mask1);
        edc_tmp[2] = ^(word_in & mask2);
        edc_tmp[3] = ^(word_in & mask3);
        edc_tmp[4] = ^(word_in & mask4);
        edc_tmp[5] = ^(word_in & mask5);
        edc_tmp[6] = ^(word_in & mask6);
        edc_tmp[7] = ^(word_in & mask7);

        // Overall parity is the XOR of encoded word and generated EDC bits
        overall_parity = (^word_in) ^ (^edc_tmp);

        // Invert last two parity bits if all-zero and all-one protection is enabled
        am_encoder = {overall_parity, ~edc_tmp[7 ], ~edc_tmp[6 ], edc_tmp[5 :0]};
    endfunction

    function [5:0] vm_encoder;
        input [11:0] data_in;

        // The word which ECC will be calculated
        logic [11:0] word_in;
        // Hold generated EDC bits
        logic [4:0] edc_tmp;
        // Overall parity for Hammming SECDED code
        logic overall_parity;

        // Masks to select bits to be XORed
        localparam mask0 = 12'b110101011011;
        localparam mask1 = 12'b011001101101;
        localparam mask2 = 12'b011110001110;
        localparam mask3 = 12'b011111110000;
        localparam mask4 = 12'b100000000000;

        // Word to encode
        word_in = data_in;

        // To generate EDC bits, pick particular word bits by using masks, then XOR them
        edc_tmp[0] = ^(word_in & mask0);
        edc_tmp[1] = ^(word_in & mask1);
        edc_tmp[2] = ^(word_in & mask2);
        edc_tmp[3] = ^(word_in & mask3);
        edc_tmp[4] = ^(word_in & mask4);

        // Overall parity is the XOR of encoded word and generated EDC bits
        overall_parity = (^word_in) ^ (^edc_tmp);

        // Invert last two parity bits if all-zero and all-one protection is enabled
        vm_encoder = {overall_parity, ~edc_tmp[4 ], ~edc_tmp[3 ], edc_tmp[2 :0]};
    endfunction
*/

`endif // } SYNTHESIS

endmodule : npu_sp_sram
// spyglass enable_block ALL

