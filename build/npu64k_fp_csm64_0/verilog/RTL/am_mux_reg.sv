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
// Top-level demo file for the AM BUS 
//
 
`include "npu_defines.v"
`include "npu_am_macros.svh"
`include "npu_am_ecc_macros.sv"
module am_mux_reg 
  import npu_types::*;
  import npu_ecc_types::*;
#(parameter NUM_AM_BANKS=2,
parameter AM_RPORTS=5+1
) 
(

// input wire signals
  input  logic       [NUM_AM_BANKS-1:0]                     am_mem_en_nxt,
  input  logic       [NUM_AM_BANKS-1:0]                     am_ls_nxt,
  input  logic       [NUM_AM_BANKS-1:0]                     am_ldst_en_nxt,
  input  am_addr_t   [NUM_AM_BANKS-1:0]                     am_addr_nxt,
  input  vyixacc_t   [NUM_AM_BANKS-1:0]                     nn_am_wr_wdata_nxt,
  input  ixambit_t   [NUM_AM_BANKS-1:0]                     nn_am_wr_wstrb_nxt,
  input  vyixacc_t   [NUM_AM_BANKS-1:0]                     am_rdata,
  input  logic       [AM_RPORTS-1:0][2:0][NUM_AM_BANKS-1:0] bank_nxt,

  input  am_ecc_c_t  [NUM_AM_BANKS-1:0]                     nn_am_wr_ecc_nxt,
  input  logic       [NUM_AM_BANKS-1:0] [AM_NUM_ECC-1:0]    nn_am_wr_ecc_wstrb_nxt,
  input  am_ecc_c_t  [NUM_AM_BANKS-1:0]                     am_recc,    
  input  logic                                              db_err_aggr,
  input  logic                                              sb_err_aggr,

// Enable ctrl signals
  input  logic       [NUM_AM_BANKS-1:0]                     am_cmd_en,
  input  logic       [NUM_AM_BANKS-1:0]                     nn_am_wr_en,
  input  logic       [NUM_AM_BANKS-1:0]                     ren,
  input  logic       [AM_RPORTS-1:0][2:0]                   bank_en,

// Output wire signals
  output logic       [NUM_AM_BANKS-1:0]                     am_mem_en_r_out,
  output logic       [NUM_AM_BANKS-1:0]                     am_ls_r_out,
  output logic       [NUM_AM_BANKS-1:0]                     am_ldst_en_r_out,
  output am_addr_t   [NUM_AM_BANKS-1:0]                     am_addr_r_out,
  output vyixacc_t   [NUM_AM_BANKS-1:0]                     nn_am_wr_wdata_r_out,
  output ixambit_t   [NUM_AM_BANKS-1:0]                     nn_am_wr_wstrb_r_out,
  output vyixacc_t   [NUM_AM_BANKS-1:0]                     nn_am_rd_rdata_r_out,
  
  output logic       [AM_RPORTS-1:0][2:0][NUM_AM_BANKS-1:0] bank_r_out,

  output am_ecc_c_t  [NUM_AM_BANKS-1:0]                     nn_am_wr_ecc_r_out,
  output logic       [NUM_AM_BANKS-1:0] [AM_NUM_ECC-1:0]    nn_am_wr_ecc_wstrb_r_out,
  output am_ecc_c_t  [NUM_AM_BANKS-1:0]                     nn_am_rd_ecc_r_out,
  output logic                                              db_err_aggr_r_out,
  output logic                                              sb_err_aggr_r_out,

  input clk,
  input rst_a

);

  logic       [NUM_AM_BANKS-1:0]     am_mem_en_r;
  logic       [NUM_AM_BANKS-1:0]     am_ls_r;
  logic       [NUM_AM_BANKS-1:0]     am_ldst_en_r;
  am_addr_t   [NUM_AM_BANKS-1:0]     am_addr_r;
  vyixacc_t   [NUM_AM_BANKS-1:0]     nn_am_wr_wdata_r;
  ixambit_t   [NUM_AM_BANKS-1:0]     nn_am_wr_wstrb_r;
  vyixacc_t   [NUM_AM_BANKS-1:0]     nn_am_rd_rdata_r;

// 3-stage delay line type onehot0 on inner dimension
typedef logic [AM_RPORTS-1:0][2:0][NUM_AM_BANKS-1:0] bank_t;

  bank_t                             bank_r;

  am_ecc_c_t  [NUM_AM_BANKS-1:0]                     nn_am_wr_ecc_r;
  logic       [NUM_AM_BANKS-1:0] [AM_NUM_ECC-1:0]    nn_am_wr_ecc_wstrb_r;
  am_ecc_c_t  [NUM_AM_BANKS-1:0]                     nn_am_rd_ecc_r; 
  logic                                              db_err_aggr_r;
  logic                                              sb_err_aggr_r;


  always_ff @(posedge clk or posedge rst_a)
  begin : mem_en_buffer_PROC
    if(rst_a ==1'b1)
    begin
      am_mem_en_r      <= '0;
      am_ls_r          <= '0;
      am_ldst_en_r     <= '0;
      am_addr_r        <= '0;
      nn_am_wr_wdata_r <= '0;
      nn_am_wr_wstrb_r <= '0;
      nn_am_rd_rdata_r <= 'b0;
    end
    else
    begin
      am_mem_en_r <= am_mem_en_nxt;
      am_ls_r     <= am_ls_nxt;
      for (int n=0; n<NUM_AM_BANKS; n++) begin 
        if (am_cmd_en[n]) begin
          am_ldst_en_r[n] <= am_ldst_en_nxt[n];
          am_addr_r[n] <= am_addr_nxt[n];
        end
        if (nn_am_wr_en[n]) begin
          nn_am_wr_wdata_r[n] <= nn_am_wr_wdata_nxt[n];
          nn_am_wr_wstrb_r[n] <= nn_am_wr_wstrb_nxt[n];
        end
        if (ren[n])
        begin
          nn_am_rd_rdata_r[n] <= am_rdata[n];
        end
      end
    end
  end : mem_en_buffer_PROC

  always_ff @(posedge clk or posedge rst_a)
  begin : mem_ecc_buffer_PROC
    if(rst_a ==1'b1)
    begin
      nn_am_wr_ecc_r       <= '0;
      nn_am_wr_ecc_wstrb_r <= '0;
      nn_am_rd_ecc_r       <= '0;
    end
    else
    begin
      for (int n=0; n<NUM_AM_BANKS; n++) begin
        if (nn_am_wr_en[n]) begin
          nn_am_wr_ecc_r[n]       <= nn_am_wr_ecc_nxt[n];
          nn_am_wr_ecc_wstrb_r[n] <= nn_am_wr_ecc_wstrb_nxt[n];
        end
        if (ren[n])
        begin
          nn_am_rd_ecc_r[n]  <= am_recc[n];
        end
      end
    end
  end : mem_ecc_buffer_PROC

/////////////buffer memory enable signal, read data and write data for one cycle////////////////////
//
  always @(posedge clk or posedge rst_a)
  begin: mem_ecc_err_PROC
    if (rst_a == 1'b1)
    begin
      sb_err_aggr_r   <= '0;
      db_err_aggr_r   <= '0;
    end  
    else
    begin
      sb_err_aggr_r   <= sb_err_aggr;
      db_err_aggr_r   <= db_err_aggr;
    end  
  end // mem_ecc_err_PROC

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
      for (int n=0; n<AM_RPORTS; n++) 
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

// Output assign
  assign am_mem_en_r_out      = am_mem_en_r;
  assign am_ls_r_out          = am_ls_r;
  assign am_ldst_en_r_out     = am_ldst_en_r;
  assign am_addr_r_out        = am_addr_r;
  assign nn_am_wr_wdata_r_out = nn_am_wr_wdata_r;
  assign nn_am_wr_wstrb_r_out = nn_am_wr_wstrb_r;
  assign nn_am_rd_rdata_r_out = nn_am_rd_rdata_r;

  assign bank_r_out           = bank_r;

  assign nn_am_wr_ecc_r_out       = nn_am_wr_ecc_r;
  assign nn_am_wr_ecc_wstrb_r_out = nn_am_wr_ecc_wstrb_r;
  assign nn_am_rd_ecc_r_out       = nn_am_rd_ecc_r;  
  assign db_err_aggr_r_out        = db_err_aggr_r;
  assign sb_err_aggr_r_out        = sb_err_aggr_r;

endmodule : am_mux_reg
