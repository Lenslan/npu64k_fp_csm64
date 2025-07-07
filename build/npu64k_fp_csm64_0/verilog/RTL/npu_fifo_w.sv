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

// vcs -sverilog npu_fifo_w.sv

`include "npu_defines.v"
`include "npu_macros.svh"
module npu_fifo_w
  #(
    parameter int FIFO_DATA_WIDTH = 8,
    parameter int FIFO_SIZEL2     = 2
  )
  (
   input  logic                        write_clk,
   input  logic                        write_rst,
   input  logic                        write_soft_rst,
   input  logic                        write_valid,
   output logic                        write_accept,
   input  logic [FIFO_DATA_WIDTH-1:0]  write_data,
   input  logic [`NUM_FLANES(FIFO_DATA_WIDTH)-1:0][(1<<FIFO_SIZEL2)-1:0] rdpnt,
   output logic [FIFO_DATA_WIDTH-1:0]  rdata,
   output logic [FIFO_SIZEL2:0]        wpnt,
   input  logic [FIFO_SIZEL2:0]        rpnt
   );
  localparam int FIFO_SIZE = 1<<FIFO_SIZEL2;

  // gray to binary and vv conversion functions
  function automatic logic [FIFO_SIZEL2:0] bin_to_gray(input logic [FIFO_SIZEL2:0] bin_value);
    begin : gray_to_bin_body
      int i;
      bin_to_gray = 0;
      bin_to_gray[FIFO_SIZEL2] = bin_value[FIFO_SIZEL2];
      for (i = FIFO_SIZEL2-1; i >= 0; i--)
        bin_to_gray[i] = bin_value[i + 1] ^ bin_value[i];
    end : gray_to_bin_body
  endfunction : bin_to_gray

  // local wires
  logic [FIFO_SIZEL2:0]                      wr_pnt_r;
  logic [FIFO_SIZE-1:0]                      wr_addr_r;
  logic [FIFO_SIZEL2:0]                      wr_pnt_nxt;
  logic [FIFO_SIZE-1:0]                      wr_addr_nxt;
  logic                                      en;
  logic [FIFO_SIZE-1:0]                      wen;
  logic [FIFO_SIZE-1:0][FIFO_DATA_WIDTH-1:0] fifo_data_r;
  logic [FIFO_SIZE-1:0][FIFO_DATA_WIDTH-1:0] data_rst_val;


  // assignments
  assign wpnt         = wr_pnt_r;
  assign write_accept = (wr_pnt_r != (write_soft_rst ? bin_to_gray(FIFO_SIZE) :rpnt)); //to keep the same value as async_fifo when pwr_dwn
  assign en           = write_soft_rst | (write_valid && write_accept);
  assign wen          = en ? wr_addr_r : '0;


// spyglass disable_block W553
// SMD:Driver Multiple times
// SJ :Reviewed, design as expected
  // combinatorial read process
  // outputs: rdata
  for (genvar gc = 0; gc < `NUM_FLANES(FIFO_DATA_WIDTH)-1; gc++)
  begin : rd_GEN
    always_comb
    begin : r_PROC
      rdata[`FRANGE(gc)] = '0;
      for (int i = 0; i < FIFO_SIZE; i++)
      begin
        rdata[`FRANGE(gc)] |= rdpnt[gc][i] ? fifo_data_r[i][`FRANGE(gc)] : '0;
      end
    end
  end : rd_GEN
  // last chunck
  always_comb
  begin : r_PROC
    rdata[`FRANGELAST(FIFO_DATA_WIDTH)] = '0;
    for (int i = 0; i < FIFO_SIZE; i++)
    begin
      rdata[`FRANGELAST(FIFO_DATA_WIDTH)] |= rdpnt[`NUM_FLANES(FIFO_DATA_WIDTH)-1][i] ? fifo_data_r[i][`FRANGELAST(FIFO_DATA_WIDTH)] : '0;
    end
  end : r_PROC
// spyglass enable_block W553

  assign wr_pnt_nxt  = write_soft_rst ?           '0 : wr_pnt_r+'d1;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
  assign wr_addr_nxt = write_soft_rst ? unsigned'(1) : { wr_addr_r, wr_addr_r[FIFO_SIZE-1] };
// spyglass enable_block W164a


  assign data_rst_val = '0;

  // write state
  // outputs: wr_pnt_r, wr_addr_r, fifo_data_r
// spyglass disable_block Reset_check07
//SMD: Clear Pins driven by comb logic
//SJ : Reset from npu_reset_ctrl BCM99 module
  always_ff @(posedge write_clk or
              posedge write_rst)
  begin : wr_proc
    if (write_rst == 1'b1) 
    begin
      wr_pnt_r         <= '0;
      wr_addr_r        <= unsigned'(1);
      fifo_data_r      <= data_rst_val;
    end
    else 
    begin 
      for (int e = 0; e < FIFO_SIZE; e++)
      begin
        if (wen[e])
        begin
          fifo_data_r[e] <= write_data;
        end
      end
      if (en)
      begin
        wr_pnt_r  <= wr_pnt_nxt;
        wr_addr_r <= wr_addr_nxt;
      end
    end
  end : wr_proc
// spyglass enable_block Reset_check07
  
endmodule : npu_fifo_w
