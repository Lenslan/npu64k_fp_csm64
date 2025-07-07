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

//
// Top-level demo file for the VM MUX 
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_vm_ecc_macros.sv"
module vm_mux_reg 
  import npu_types::*;
  import npu_ecc_types::*;
#(parameter NUM_VM_BANKS=((VSIZE==8)?32:16),
parameter VM_RPORTS=(((NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES+DMA_VM_LANES)+1)+1)
) 
(

// input wire signals
  input  logic       [NUM_VM_BANKS-1:0]                     vm_mem_en_nxt,
  input  logic       [NUM_VM_BANKS-1:0]                     vm_ls_nxt,
  input  logic       [NUM_VM_BANKS-1:0]                     vm_ldst_en_nxt,
  input  vm_addr_t   [NUM_VM_BANKS-1:0]                     vm_addr_nxt,
  input  ixpix_t     [NUM_VM_BANKS-1:0]                     nn_vm_wr_wdata_nxt,
  input  ixbit_t     [NUM_VM_BANKS-1:0]                     nn_vm_wr_wstrb_nxt,
  input  ixpix_t     [NUM_VM_BANKS-1:0]                     vm_rdata,
  input  logic       [VM_RPORTS-1:0][2:0][NUM_VM_BANKS-1:0] bank_nxt,

  input  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                     nn_vm_wr_ecc_nxt,
  input  logic       [NUM_VM_BANKS-1:0] [VM_NUM_ECC-1:0]    nn_vm_wr_ecc_wstrb_nxt,
  input  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                     vm_recc,
  input  logic                                              db_err_aggr,
  input  logic                                              sb_err_aggr,

// Enable ctrl signals
  input  logic       [NUM_VM_BANKS-1:0]                     vm_cmd_en,
  input  logic       [NUM_VM_BANKS-1:0]                     nn_vm_wr_en,
  input  logic       [NUM_VM_BANKS-1:0]                     ren,
  input  logic       [VM_RPORTS-1:0][2:0]                   bank_en,

// output wire signals  
  output logic       [NUM_VM_BANKS-1:0]                     vm_mem_en_r_out,
  output logic       [NUM_VM_BANKS-1:0]                     vm_ls_r_out,
  output logic       [NUM_VM_BANKS-1:0]                     vm_ldst_en_r_out,
  output vm_addr_t   [NUM_VM_BANKS-1:0]                     vm_addr_r_out,
  output ixpix_t     [NUM_VM_BANKS-1:0]                     nn_vm_wr_wdata_r_out,
  output ixbit_t     [NUM_VM_BANKS-1:0]                     nn_vm_wr_wstrb_r_out,
  output ixpix_t     [NUM_VM_BANKS-1:0]                     nn_vm_rd_rdata_r_out,
  
  output logic       [VM_RPORTS-1:0][2:0][NUM_VM_BANKS-1:0] bank_r_out,

  output vm_ecc_c_t  [NUM_VM_BANKS-1:0]                     nn_vm_wr_ecc_r_out,
  output logic       [NUM_VM_BANKS-1:0] [VM_NUM_ECC-1:0]    nn_vm_wr_ecc_wstrb_r_out,
  output vm_ecc_c_t  [NUM_VM_BANKS-1:0]                     nn_vm_rd_ecc_r_out,
  output logic                                              db_err_aggr_r_out,
  output logic                                              sb_err_aggr_r_out,

  input clk,
  input rst_a
  
);

  logic       [NUM_VM_BANKS-1:0]     vm_mem_en_r;
  logic       [NUM_VM_BANKS-1:0]     vm_ls_r;
  logic       [NUM_VM_BANKS-1:0]     vm_ldst_en_r;
  vm_addr_t   [NUM_VM_BANKS-1:0]     vm_addr_r;
  ixpix_t     [NUM_VM_BANKS-1:0]     nn_vm_wr_wdata_r;
  ixbit_t     [NUM_VM_BANKS-1:0]     nn_vm_wr_wstrb_r;
  ixpix_t     [NUM_VM_BANKS-1:0]     nn_vm_rd_rdata_r;

// 3-stage delay line type onehot0 on inner dimension
typedef logic [VM_RPORTS-1:0][2:0][NUM_VM_BANKS-1:0] bank_t;

  bank_t                             bank_r;

  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                     nn_vm_wr_ecc_r;
  logic       [NUM_VM_BANKS-1:0] [VM_NUM_ECC-1:0]    nn_vm_wr_ecc_wstrb_r;
  vm_ecc_c_t  [NUM_VM_BANKS-1:0]                     nn_vm_rd_ecc_r; 
  logic                                              db_err_aggr_r;
  logic                                              sb_err_aggr_r;

//////////////buffer memory enable signal, read data and write data for one cycle////////////////////
//
  always_ff @(posedge clk or posedge rst_a)
  begin : mem_en_buffer_PROC
    if (rst_a ==1'b1)
    begin
      vm_mem_en_r             <= '0;
      vm_ls_r                 <= '1;
      vm_ldst_en_r            <= '0;
      vm_addr_r               <= '0;
      nn_vm_wr_wdata_r        <= '0;
      nn_vm_wr_wstrb_r        <= '0;
      nn_vm_rd_rdata_r        <= 'b0;
    end
    else
    begin
      vm_mem_en_r             <= vm_mem_en_nxt;
      vm_ls_r                 <= vm_ls_nxt;
      for (int n=0; n<NUM_VM_BANKS; n++) 
      begin 
        if (vm_cmd_en[n]) 
        begin
          vm_ldst_en_r[n]     <= vm_ldst_en_nxt[n];
          vm_addr_r[n]        <= vm_addr_nxt[n];
        end
        if (nn_vm_wr_en[n]) 
        begin
          nn_vm_wr_wdata_r[n] <= nn_vm_wr_wdata_nxt[n];
          nn_vm_wr_wstrb_r[n] <= nn_vm_wr_wstrb_nxt[n];
        end
        if (ren[n])
        begin
          nn_vm_rd_rdata_r[n] <= vm_rdata[n];
        end
      end
    end
  end : mem_en_buffer_PROC

//////////////hold port massege two cycle for loading request//////////////
//
  always_ff @(posedge clk or posedge rst_a)
  begin: bank_msg_buffer_PROC
    if (rst_a == 1'b1)
    begin
      bank_r  <= '0;
    end
    else 
    begin
      for (int n=0; n<VM_RPORTS; n++) 
      begin //{
        for (int i=0; i<3; i++) 
        begin 
          if (bank_en[n][i])
          begin
            bank_r[n][i] <= bank_nxt[n][i];
          end
        end
      end
    end
  end : bank_msg_buffer_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin : mem_ecc_buffer_PROC
    if (rst_a ==1'b1)
    begin
      nn_vm_wr_ecc_r          <= '0;
      nn_vm_wr_ecc_wstrb_r    <= '0;
      nn_vm_rd_ecc_r          <= '0;
    end
    else
    begin
      for (int n=0; n<NUM_VM_BANKS; n++) 
      begin
        if (nn_vm_wr_en[n]) 
        begin
          nn_vm_wr_ecc_r[n]       <= nn_vm_wr_ecc_nxt[n];
          nn_vm_wr_ecc_wstrb_r[n] <= nn_vm_wr_ecc_wstrb_nxt[n];
        end
        if (ren[n])
        begin
          nn_vm_rd_ecc_r[n]       <= vm_recc[n];
        end
      end
    end
  end : mem_ecc_buffer_PROC
  always_ff @(posedge clk or posedge rst_a)
  begin : mem_ecc_err_PROC
    if (rst_a ==1'b1)
    begin
      db_err_aggr_r  <= '0;
      sb_err_aggr_r  <= '0;
    end
    else
    begin
      db_err_aggr_r  <= db_err_aggr;
      sb_err_aggr_r  <= sb_err_aggr;
    end
  end : mem_ecc_err_PROC
// Output assign
  assign vm_mem_en_r_out      = vm_mem_en_r;
  assign vm_ls_r_out          = vm_ls_r;
  assign vm_ldst_en_r_out     = vm_ldst_en_r;
  assign vm_addr_r_out        = vm_addr_r;
  assign nn_vm_wr_wdata_r_out = nn_vm_wr_wdata_r;
  assign nn_vm_wr_wstrb_r_out = nn_vm_wr_wstrb_r;
  assign nn_vm_rd_rdata_r_out = nn_vm_rd_rdata_r;

  assign bank_r_out           = bank_r;

  assign nn_vm_wr_ecc_r_out       = nn_vm_wr_ecc_r;
  assign nn_vm_wr_ecc_wstrb_r_out = nn_vm_wr_ecc_wstrb_r;
  assign nn_vm_rd_ecc_r_out       = nn_vm_rd_ecc_r;
  assign db_err_aggr_r_out        = db_err_aggr_r;
  assign sb_err_aggr_r_out        = sb_err_aggr_r;

endmodule : vm_mux_reg
