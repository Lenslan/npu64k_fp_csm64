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

`include "npu_defines.v"

`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"

`include "npu_sram_defines.sv"

`include "npu_vm_ecc_macros.sv"
`include "npu_am_ecc_macros.sv"

module npu_srams
  import npu_types::*;
  import npu_ecc_types::*;
 #(parameter NUM_VM_BANKS=4*VSIZE
  )
(
   // VM Read/Write
// spyglass disable_block W240
//SMD:Unread input
//SJ : some bits of am_addr and vm_addr are not read and ignore
   `VMSLV(NUM_VM_BANKS,vm_),
   // AM Read/Write (2 lanes)
   `AMSLV_MSK(2,am_),
   `VMSLV_ECC(NUM_VM_BANKS,vm_),
   `AMSLV_ECC(2,am_),
   // clock and reset
   input logic             pd_mem,
   input logic             clk,                     // clock, all logic clocked at posedge
   input logic             rst_a                    // asynchronous reset, active high
// spyglass enable_block W240
);

  // | NPU_SLICE_MEM | AM size | VM size | AM_ADDR_W | VM_ADDR_W |
  // | ------------- | ------- | ------- | --------- | --------- |
  // |     0         | 64KB    | 256KB   |    6      |    9      |
  // |     1         | 128KB   | 256KB   |    7      |    9      |
  // |     2         | 128KB   | 512KB   |    7      |   10      |
  // |     3         | 32KB    | 128KB   |    7      |    9      |
  localparam int VM_ADDR_W   = 10;
  localparam int VM_ADDR_MSB = VM_ADDR_W - 1;
  localparam int VM_BK_DW  = PIX_W*ISIZE;
  localparam int VM_BK_CW  = VM_NUM_ECC*VM_ECC_UNIT_CW; // ecc check bit with

  genvar gvr_i;
  generate
    for(gvr_i = 0; gvr_i < NUM_VM_BANKS; gvr_i = gvr_i + 1)
    begin: vm_inst
      logic [VM_BK_DW-1:0] vm_wr_tmp, vm_rd_tmp;
      logic [VM_BK_CW-1:0] vm_wr_ecc_tmp, vm_rd_ecc_tmp;
      assign vm_wr_ecc_tmp = vm_wecc[gvr_i];
      assign vm_recc[gvr_i] = vm_rd_ecc_tmp;
      assign vm_wr_tmp = vm_wdata[gvr_i];
      assign vm_rdata[gvr_i] = vm_rd_tmp;
      npu_mem_vec_bank
      #(
         .MEM_TARGET(`NPU_MEM_TARGET_VM),
         .ADDR_WIDTH(VM_ADDR_W),
         .DATA_WIDTH($bits(vm_ecc_t)),
         .MASK_WIDTH(ISIZE + VM_NUM_ECC)
      ) u_npu_mem_vec_bank (
         .clk             (clk),
         .mem_en          (vm_mem_en[gvr_i]),
         .wr_en           (vm_ldst_en[gvr_i]),
         .addr            (vm_addr[gvr_i][VM_ADDR_MSB:0]),
         .wr_data         ({vm_wr_ecc_tmp[VM_ECC_UNIT_CW+:VM_ECC_UNIT_CW],vm_wr_tmp[VM_ECC_UNIT_DW+:VM_ECC_UNIT_DW]
                           ,vm_wr_ecc_tmp[0+:VM_ECC_UNIT_CW],vm_wr_tmp[0+:VM_ECC_UNIT_DW]}),
         .wr_mask         ({vm_ecc_wstrb[gvr_i][(VM_NUM_ECC/2)+:(VM_NUM_ECC/2)],vm_wstrb[gvr_i][(ISIZE/2)+:(ISIZE/2)]
                           ,vm_ecc_wstrb[gvr_i][0+:(VM_NUM_ECC/2)],vm_wstrb[gvr_i][0+:(ISIZE/2)]}),
         .rd_data         ({vm_rd_ecc_tmp[VM_ECC_UNIT_CW+:VM_ECC_UNIT_CW],vm_rd_tmp[VM_ECC_UNIT_DW+:VM_ECC_UNIT_DW]
                           ,vm_rd_ecc_tmp[0+:VM_ECC_UNIT_CW],vm_rd_tmp[0+:VM_ECC_UNIT_DW]}),
         .ds              (vm_ds[gvr_i]),
         .sd              (pd_mem),
         .ls              (vm_ls[gvr_i])
       );
    end : vm_inst
  endgenerate

  localparam int AM_ADDR_W   = 7;
  localparam int AM_ADDR_MSB = AM_ADDR_W - 1;

  localparam int NUM_AM_BANKS = 2;
  localparam int AM_SLICES = 16;
  localparam int AM_BK_DW  = VSIZE*ISIZE*ACC_W;
  localparam int AM_SL_DW  = AM_BK_DW / AM_SLICES; // slice data width
  localparam int AM_SL_MW  = AM_SL_DW / ACC_W;     // slice mask width
  localparam int AM_BK_MW  = AM_SL_MW*AM_SLICES;   // total mask width

  localparam int ACC_BW   = ACC_W/8; // accumulator byte width
  localparam int AM_BK_C_DW  = AM_NUM_ECC*AM_ECC_UNIT_CW; // ecc check bit with
  localparam int AM_BK_C_MW  = AM_NUM_ECC; // ecc check bit with
  localparam int AM_SL_C_DW  = (AM_BK_C_DW/AM_SLICES); // slice ecc check bit width
  localparam int AM_SL_C_MW  = (AM_NUM_ECC/AM_SLICES); // slice ecc check bit width
  genvar gvr_j, gvr_k;
  generate
    // For each logical bank (separately addressable)
    for(gvr_j = 0; gvr_j < NUM_AM_BANKS; gvr_j = gvr_j + 1)
    begin: am_inst_bank
      logic [AM_BK_DW-1:0] wr_tmp, rd_tmp;
      logic [AM_BK_MW-1:0] wr_msk_tmp;
      logic [AM_BK_C_DW-1:0] wr_ecc_tmp, rd_ecc_tmp;
      logic [AM_BK_C_MW-1:0] wr_ecc_wstrb_tmp;
      logic [AM_SL_DW+AM_SL_C_DW-1:0] wr_sl_tmp;
      assign wr_ecc_tmp = am_wecc[gvr_j];
      assign wr_ecc_wstrb_tmp = am_ecc_wstrb[gvr_j];
      assign am_recc[gvr_j] = rd_ecc_tmp;
      assign wr_tmp = am_wdata[gvr_j];
      assign wr_msk_tmp = am_wstrb[gvr_j];
      assign am_rdata[gvr_j] = rd_tmp;
      // Slice up the logical bank data into narrower instances
      // Broadcast the address
      for(gvr_k = 0; gvr_k < AM_SLICES; gvr_k = gvr_k + 1)
      begin: am_inst_slice
        logic [(AM_SL_DW+(AM_NUM_ECC*8)/AM_SLICES)-1:0]     wr_sl_tmp;
        logic [AM_SL_MW*(ACC_W/8)+AM_SL_C_MW-1:0]       wr_msk_sl_tmp;
        logic [(AM_SL_DW+(AM_NUM_ECC*8)/AM_SLICES)-1:0]     rd_sl_tmp;

        for(genvar i = 0; i < AM_SL_DW/AM_ECC_UNIT_DW; i++)
        begin
          assign wr_sl_tmp[(AM_ECC_UNIT_DW+AM_ECC_UNIT_CW)*i+:(AM_ECC_UNIT_DW+AM_ECC_UNIT_CW)] = { wr_ecc_tmp[(gvr_k*AM_SL_C_DW + AM_ECC_UNIT_CW*i ) +: AM_ECC_UNIT_CW]
                                                                                                  ,wr_tmp[(gvr_k*AM_SL_DW + AM_ECC_UNIT_DW*i) +: AM_ECC_UNIT_DW]};
          assign rd_ecc_tmp[(gvr_k*AM_SL_C_DW + AM_ECC_UNIT_CW*i ) +: AM_ECC_UNIT_CW] = rd_sl_tmp[((AM_ECC_UNIT_DW+AM_ECC_UNIT_CW)*i+AM_ECC_UNIT_DW)+:AM_ECC_UNIT_CW];
          assign rd_tmp[(gvr_k*AM_SL_DW + AM_ECC_UNIT_DW*i) +: AM_ECC_UNIT_DW] = rd_sl_tmp[(AM_ECC_UNIT_DW+AM_ECC_UNIT_CW)*i+:AM_ECC_UNIT_DW];
          assign wr_msk_sl_tmp[(AM_ECC_UNIT_DW/8+1)*i+:(AM_ECC_UNIT_DW/8+1)] = {wr_ecc_wstrb_tmp[(gvr_k*(AM_SL_C_MW) + 1*i)+:1]
                                                                              ,{ACC_BW{wr_msk_tmp[(gvr_k*AM_SL_MW + 1*(2*i+1) )+:1]}}
                                                                              ,{ACC_BW{wr_msk_tmp[(gvr_k*AM_SL_MW + 1*(2*i) )  +:1]}}};
        end
        npu_mem_acc_bank
        #(
          .MEM_TARGET(`NPU_MEM_TARGET_AM),
          .ADDR_WIDTH(AM_ADDR_W),
          .DATA_WIDTH(AM_SL_DW+AM_SL_C_DW),
          .MASK_WIDTH(AM_SL_MW*(ACC_W/8)+AM_SL_C_MW)
        ) u_npu_mem_acc_bank (
          .clk             (clk),
          .mem_en          (am_mem_en[gvr_j]),
          .wr_en           (am_ldst_en[gvr_j]),
          .addr            (am_addr[gvr_j][AM_ADDR_MSB:0]),
          .wr_data         (wr_sl_tmp),
          .wr_mask         (wr_msk_sl_tmp),
          .rd_data         (rd_sl_tmp),
          .ds              (am_ds[gvr_j]),
          .sd              (pd_mem),
          .ls              (am_ls[gvr_j])
        );
      end: am_inst_slice
  end : am_inst_bank
  endgenerate

endmodule : npu_srams
