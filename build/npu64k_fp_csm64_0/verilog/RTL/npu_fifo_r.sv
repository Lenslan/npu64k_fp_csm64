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
`include "npu_macros.svh"
module npu_fifo_r
  #(
    parameter int FIFO_DATA_WIDTH = 8,
    parameter int FIFO_SIZEL2     = 2
  )
  (
   input  logic                        read_clk,
   input  logic                        read_rst,
   input  logic                        read_soft_rst,
   output logic                        read_valid,
   input  logic                        read_accept,
   output logic [FIFO_DATA_WIDTH-1:0]  read_data,
   output logic [`NUM_FLANES(FIFO_DATA_WIDTH)-1:0][(1<<FIFO_SIZEL2)-1:0] rdpnt,
   input  logic [FIFO_DATA_WIDTH-1:0]  rdata,
   input  logic [FIFO_SIZEL2:0]        wpnt,
   output logic [FIFO_SIZEL2:0]        rpnt
   );
  localparam int FIFO_SIZE = 1<<FIFO_SIZEL2;

  // local wires
  logic                       en;
  logic [FIFO_SIZEL2:0]       rd_pnt_r;
  logic [FIFO_SIZEL2:0]       rd_shadow_r;
  logic [FIFO_SIZE-1:0]       rd_addr_r;
  logic [FIFO_SIZEL2:0]       rd_pnt_nxt;
  logic [FIFO_SIZEL2:0]       rd_shadow_nxt;
  logic [FIFO_SIZE-1:0]       rd_addr_nxt;
  logic                       readi_valid;
  logic                       readi_accept;
  logic [FIFO_DATA_WIDTH-1:0] readi_data;
  logic [FIFO_DATA_WIDTH-1:0] read_data_r;
  logic                       read_valid_r;
  logic                       read_valid_nxt;
  logic [FIFO_DATA_WIDTH-1:0] data_rst_val;

  // assignments
  assign en             = read_soft_rst | (readi_valid & readi_accept);
  assign rdpnt          = {(`NUM_FLANES(FIFO_DATA_WIDTH)){rd_addr_r}};
  assign rpnt           = rd_shadow_r;
  assign readi_valid    = ((read_soft_rst ? '0 : wpnt) != rd_pnt_r);
  assign rd_pnt_nxt     = read_soft_rst ? '0                     : rd_pnt_r+'d1;
  assign rd_shadow_nxt  = read_soft_rst ? unsigned'(FIFO_SIZE)   : rd_shadow_r+'d1;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
  assign rd_addr_nxt    = read_soft_rst ? unsigned'(1)           : { rd_addr_r, rd_addr_r[FIFO_SIZE-1] };
// spyglass enable_block W164a
  assign read_valid_nxt = (~read_soft_rst) & ((read_valid_r & ~read_accept) | readi_valid);
  assign readi_accept   = read_accept | (~read_valid_r);
  assign read_valid     = read_valid_r;
  assign read_data      = read_data_r;

  assign data_rst_val = '0;

  // read state
  // outputs: rd_pnt_r, rd_shadow_r, rd_addr_r, read_valid_r, read_data_r
  always_ff @(posedge read_clk or
              posedge read_rst)
  begin : rd_proc
    if (read_rst == 1'b1)
    begin
      rd_pnt_r      <= '0;
      rd_shadow_r   <= unsigned'(FIFO_SIZE);
      rd_addr_r     <= unsigned'(1);
      read_valid_r  <= 1'b0;
      read_data_r   <= data_rst_val;
    end
    else 
    begin
      read_valid_r  <= read_valid_nxt;
      if (en) begin
        rd_pnt_r    <= rd_pnt_nxt;
        rd_shadow_r <= rd_shadow_nxt;
        rd_addr_r   <= rd_addr_nxt;
      end
      if (readi_valid & readi_accept) begin
        read_data_r <= rdata;
      end
    end
  end : rd_proc
  
endmodule : npu_fifo_r
