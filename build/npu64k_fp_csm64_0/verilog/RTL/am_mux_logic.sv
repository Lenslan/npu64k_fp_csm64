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

`ifndef NPU_ECC_TYPES_IMPORTED
`define NPU_ECC_TYPES_IMPORTED
import npu_ecc_types::*;
`endif  
module am_mux_logic
  import npu_types::*;
  import npu_ecc_types::*;
  #(
    parameter AM_RPORTS=5+1,
    parameter AM_WPORTS=4+1,
    parameter NUM_AM_BANKS=2
   )
  (
   //
   // interfaces
   //
   // write request
   input  logic     [AM_WPORTS-1:0]     nn_am_wr_cmd_valid,  // write command valid
   output logic     [AM_WPORTS-1:0]     nn_am_wr_cmd_accept, // write command accept
   input  am_addr_t [AM_WPORTS-1:0]     nn_am_wr_cmd_addr,   // write command address
   // write data channel
   input  ixambit_t [AM_WPORTS-1:0]     nn_am_wr_wstrb,      // write strobe
   // read request
   input  logic     [AM_RPORTS-1:0]     nn_am_rd_cmd_valid,  // read command valid
   output logic     [AM_RPORTS-1:0]     nn_am_rd_cmd_accept, // read command accept
   input  am_addr_t [AM_RPORTS-1:0]     nn_am_rd_cmd_addr,   // read command address
   // read data channel
   output logic     [AM_RPORTS-1:0]     nn_am_rd_rvalid,     // read data valid

   input  logic     [NUM_AM_BANKS-1:0]  am_mem_en,           // load enable
   
   //
   // am ecc
   //
   input  logic          am_prot_en,
   output logic       [NUM_AM_BANKS-1:0] [AM_NUM_ECC-1:0]    nn_am_wr_ecc_wstrb_nxt,  // port2bank write ecc msk

// input signals
   input  logic       [AM_RPORTS-1:0][2:0][NUM_AM_BANKS-1:0] bank_r,

// output signals
   output logic       [AM_RPORTS-1:0][2:0]                   bank_en,            
   output logic       [AM_RPORTS-1:0][2:0][NUM_AM_BANKS-1:0] bank_nxt,           
   output logic       [NUM_AM_BANKS-1:0]                     am_mem_en_nxt,      
   output logic       [NUM_AM_BANKS-1:0]                     am_cmd_en,          
   output logic       [NUM_AM_BANKS-1:0]                     am_ldst_en_nxt,       
   output ixambit_t   [NUM_AM_BANKS-1:0]                     nn_am_wr_wstrb_nxt, 
   output logic       [NUM_AM_BANKS-1:0]                     nn_am_wr_en,
   output logic       [NUM_AM_BANKS-1:0]                     ren,
   output logic       [NUM_AM_BANKS-1:0]                     am_ls_nxt,

   // am initialization
   input logic      am_init,
   //
   // clock and rst_a
   //
   input logic      clk,                   // clock, all logic clocked at posedge
   input logic      rst_a                  // asynchronous rst_a, active high


  );

  localparam AM_PORTS_WIDTH=$clog2(NUM_AM_BANKS);

  // mem ecc
  logic       [$bits(ixambit_t)-1:0]              wr_msk_tmp;
  logic mem_ecc_en;
  assign mem_ecc_en = am_prot_en;

  // light sleep when memory access is done
  assign am_ls_nxt = ~(am_mem_en_nxt | am_mem_en);
  
  logic f;
  logic [$bits(ixambit_t)-1:0] am_wr_wstrb_tmp;
  always_comb
  begin : am_bus_ack_PROC

    bank_en             = '0;
    bank_nxt            = '0;
    am_mem_en_nxt       = '0;
    am_cmd_en           = '0;
    am_ldst_en_nxt      = '0;
    nn_am_rd_cmd_accept = '0;
    nn_am_wr_cmd_accept = '0;
    nn_am_wr_wstrb_nxt  = '0;
    nn_am_wr_en         = '0;
    am_wr_wstrb_tmp     = '1;

    // shift bank next
    for (int r = 0; r < AM_RPORTS; r++)
    begin
      bank_nxt[r][2:1] = bank_r[r][1:0];
      bank_en[r][2]    = bank_r[r][2:1] != '0;
      bank_en[r][1]    = bank_r[r][1:0] != '0;
      bank_en[r][0]    = bank_r[r][0]   != '0;
    end

// spyglass disable_block W362
//SMD:Width mismatch
//SJ :Ignore $unsigned(i) int index operation in loop
    for (int i=0; i<NUM_AM_BANKS; i++)
    begin //{
      if (am_init)
      begin //{
        am_mem_en_nxt[i]                  |= 1'b1;
        am_cmd_en[i]                      |= 1'b1;
        am_ldst_en_nxt[i]                 |= 1'b1;
        nn_am_wr_en[i]                    |= 1'b1;
        nn_am_wr_wstrb_nxt[i]             |= am_wr_wstrb_tmp;
      end //}
      f = 1'b0;
      // conv read has highest priority
      if ((nn_am_rd_cmd_addr[0][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_rd_cmd_valid[0]) 
      begin    //select read operation
        nn_am_rd_cmd_accept[0]            |= ~f;              //accept read
        bank_en[0][0]                     |= ~f;            
        bank_nxt[0][0][i]                 |= ~f;              //record port info for data return
        am_mem_en_nxt[i]                  |= 1'b1;
        am_cmd_en[i]                      |= 1'b1;            //enable command
        f                                 |= 1'b1;
      end
      // conv write has second highest priority
      if ((nn_am_wr_cmd_addr[0][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_wr_cmd_valid[0]) 
      begin // select write operation
        nn_am_wr_cmd_accept[0]            |= ~f;              //accept axi read
        am_mem_en_nxt[i]                  |= 1'b1;
        am_cmd_en[i]                      |= 1'b1;            //enable command 
        am_ldst_en_nxt[i]                 |= ~f;
        nn_am_wr_en[i]                    |= ~f;
        nn_am_wr_wstrb_nxt[i]             |= f ? '0 : nn_am_wr_wstrb[0];
        f                                 |= 1'b1;
      end
      // gtoa read has third highest priority
      if ((nn_am_rd_cmd_addr[1][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_rd_cmd_valid[1]) 
      begin    //select read operation
        nn_am_rd_cmd_accept[1]            |= ~f;              //accept read
        bank_en[1][0]                     |= ~f;            
        bank_nxt[1][0][i]                 |= ~f;              //record port info for data return
        am_mem_en_nxt[i]                  |= 1'b1;
        am_cmd_en[i]                      |= 1'b1;            //enable command
        f                                 |= 1'b1;
      end
      // gtoa write has fourth highest priority
      if ((nn_am_wr_cmd_addr[1][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_wr_cmd_valid[1]) 
      begin // select write operation
        nn_am_wr_cmd_accept[1]            |= ~f;              //accept axi read
        am_mem_en_nxt[i]                  |= 1'b1;
        am_cmd_en[i]                      |= 1'b1;            //enable command 
        am_ldst_en_nxt[i]                 |= ~f;
        nn_am_wr_en[i]                    |= ~f;
        nn_am_wr_wstrb_nxt[i]             |= f ? '0 : nn_am_wr_wstrb[1];
        f                                 |= 1'b1;
      end
      
      // rest
      for (int n=2; n<AM_RPORTS; n++)
      begin //{
        if ((nn_am_rd_cmd_addr[n][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_rd_cmd_valid[n]) 
        begin    //select read operation
          nn_am_rd_cmd_accept[n]          |= ~f;              //accept read
          bank_en[n][0]                   |= ~f;            
          bank_nxt[n][0][i]               |= ~f;              //record port info for data return
          am_mem_en_nxt[i]                |= 1'b1;
          am_cmd_en[i]                    |= 1'b1;            //enable command
          f                               |= 1'b1;
        end
      end //}

      for (int m=2; m<AM_WPORTS; m++)
      begin //{
        if ((nn_am_wr_cmd_addr[m][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_wr_cmd_valid[m]) 
        begin // select write operation
          nn_am_wr_cmd_accept[m]          |= ~f;              //accept axi read
          am_mem_en_nxt[i]                |= 1'b1;
          am_cmd_en[i]                    |= 1'b1;            //enable command 
          am_ldst_en_nxt[i]               |= ~f;
          nn_am_wr_en[i]                  |= ~f;
          nn_am_wr_wstrb_nxt[i]           |= f ? '0 : nn_am_wr_wstrb[m];
          f                               |= 1'b1;
        end
      end //}
    end //}
// spyglass enable_block W362
  end : am_bus_ack_PROC

  always_comb
  begin : am_ecc_PROC
    logic f;
    wr_msk_tmp          = '0;
    nn_am_wr_ecc_wstrb_nxt   = '0;

// spyglass disable_block W362
//SMD:Width mismatch
//SJ :Ignore $unsigned(i) int index operation in loop
    for (int i=0; i<NUM_AM_BANKS; i++)
    begin //{
      if (am_init)
      begin //{
        for (int j=0; j<AM_NUM_ECC; j++)
        begin    
          nn_am_wr_ecc_wstrb_nxt[i][j]   = mem_ecc_en? '1 : 1'b0;
        end
      end //}
      f = 1'b0;
      // conv read has highest priority
      if ((nn_am_rd_cmd_addr[0][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_rd_cmd_valid[0]) 
      begin    //select read operation
        f                                 |= 1'b1;
      end
      // conv write has second highest priority
      if ((nn_am_wr_cmd_addr[0][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_wr_cmd_valid[0]) 
      begin // select write operation
        wr_msk_tmp                        |= f ? '0 : nn_am_wr_wstrb[0];
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression (j * ($bits(ixambit_t) / AM_NUM_ECC))
//SJ :Ignore
        for (int j=0; j<AM_NUM_ECC; j++)
        begin    
          nn_am_wr_ecc_wstrb_nxt[i][j]   = mem_ecc_en? (|wr_msk_tmp[j*($bits(ixambit_t)/AM_NUM_ECC)+:($bits(ixambit_t)/AM_NUM_ECC)]) : 1'b0;
        end
// spyglass enable_block SelfDeterminedExpr-ML
        f                                 |= 1'b1;
      end
      // gtoa read has third highest priority
      if ((nn_am_rd_cmd_addr[1][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_rd_cmd_valid[1]) 
      begin    //select read operation
        f                                 |= 1'b1;
      end
      // gtoa write has fourth highest priority
      if ((nn_am_wr_cmd_addr[1][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_wr_cmd_valid[1]) 
      begin // select write operation
        wr_msk_tmp                        |= f ? '0 : nn_am_wr_wstrb[1];
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression (j * ($bits(ixambit_t) / AM_NUM_ECC))
//SJ :Ignore
        for (int j=0; j<AM_NUM_ECC; j++)
        begin    
          nn_am_wr_ecc_wstrb_nxt[i][j]    = mem_ecc_en? (|wr_msk_tmp[j*($bits(ixambit_t)/AM_NUM_ECC)+:($bits(ixambit_t)/AM_NUM_ECC)]) : 1'b0;
        end
// spyglass enable_block SelfDeterminedExpr-ML
        f                                 |= 1'b1;
      end
      
      // rest
      for (int n=2; n<AM_RPORTS; n++)
      begin //{
        if ((nn_am_rd_cmd_addr[n][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_rd_cmd_valid[n]) 
        begin    //select read operation
          f                               |= 1'b1;
        end
      end //}

      for (int m=2; m<AM_WPORTS; m++)
      begin //{
        if ((nn_am_wr_cmd_addr[m][AM_PORTS_WIDTH-1:0] == unsigned'(i)) && nn_am_wr_cmd_valid[m]) 
        begin // select write operation
          wr_msk_tmp                      |= f ? '0 : nn_am_wr_wstrb[m];
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression (j * ($bits(ixambit_t) / AM_NUM_ECC))
//SJ :Ignore
          for (int j=0; j<AM_NUM_ECC; j++)
          begin    
            nn_am_wr_ecc_wstrb_nxt[i][j]  |= mem_ecc_en? (|wr_msk_tmp[j*($bits(ixambit_t)/AM_NUM_ECC)+:($bits(ixambit_t)/AM_NUM_ECC)]) : 1'b0;
          end
// spyglass enable_block SelfDeterminedExpr-ML
          f                               |= 1'b1;
        end
      end //}

    end //}
// spyglass enable_block W362
  end : am_ecc_PROC 

  ///////////////////get load data and data valid/////////////////////////////
  always_comb
  begin : am_bus_rdata_PROC
    ren                 = '0;
    nn_am_rd_rvalid     = '0;
    for (int n=0; n<AM_RPORTS; n++) // {
    begin
      nn_am_rd_rvalid[n] = bank_r[n][2] != '0;
      for (int i=0; i<NUM_AM_BANKS; i++) //{
      begin
        ren[i] |= bank_r[n][1][i];         // enable read data register
      end //}
    end //}
  end : am_bus_rdata_PROC


endmodule : am_mux_logic
