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

/*
 * This module implements the bpar read module
 * the module:
 * - reads bpar from VM
 * - put bpar data into a FIFO
 * - core will request (bpar_pop_q_num)x32b parameters from FIFO at one time
 * - if the number of data contained in the FIFO is more than the number requested, parameters will be popped out
analyze -format sverilog -vcs "../../../shared/RTL/npu_types.sv ../npu_gtoa_types.sv +incdir+../../../shared/RTL ../npu_gtoa_bpar_rd.sv ../../../shared/RTL/npu_iterator.sv  ../../../shared/RTL/npu_vm_read.sv ../../../shared/RTL/npu_fifo.sv"
  */
`include "npu_defines.v"
`include "npu_vm_macros.svh"

module npu_gtoa_bpar_rd
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                       clk,             // clock
   input  logic                       rst_a,           // asynchronous reset, active high
   // input hlapi
   input  logic                       hlapi_valid,     // hlapi is valid
   output logic                       hlapi_accept,    // hlapi is accepted
   input  vm_addr_t                   hlapi_bptr,      // bpar start pointer in VM
   input  offset_t                    hlapi_bnum,      // total number of ixpix_t to read
   input  logic                       hlapi_alay,      // accumulator layout
   // VM read port
   `VMRMST(1,vm_rd_),
   // bpar pop port
   output logic                 [5:0] bpar_q_lvl,      // parameter level, max 32/4=8*ixacc_t
   input  logic                       bpar_pop_q,      // if true then pop parameters from the queue
   input  logic                 [3:0] bpar_pop_q_num,  // number of parameters to pop from queue
   output ixacc_t  [ACT_BREG_NUM-1:0] bpar_out         // per channel parameter 
   );
  // local wires
  logic                               lvl_en;          // enable level register
  logic            [5:0]              lvl_r;           // count number of issues
  logic            [5:0]              lvl_nxt;          // count number of issues
  logic            [31:0]             fifo_data_en;    // fifo register enable
  ixpix_t          [31:0]             fifo_data_r;     // fifo storage array, 31*ixpix_t (equal to 8*ixacc_t)
  logic                               hlapi_alay_en;   // enable hlapi_alay register
  logic                               hlapi_alay_r;    // hlapi_alay register
  logic                               hlapi_validi;    // hlapi valid internal
  logic                               hlapi_accepti;   // hlapi accept internal
  // fifo pointer have one extra bit as sign bit
  logic            [5:2]              rd_ptr_r;        // read pointer in 512b units
  logic            [5:2]              rd_ptr_nxt;      // read pointer next
  logic            [5:0]              wr_ptr_r;        // write pointer in 128b units
  logic            [5:0]              wr_ptr_nxt;      // write pointer next
  logic                               v_valid;         // internal output valid from VM read instance
  logic                               v_accept;        // internal output accept from VM read instance
  buf_t                               bf;              // dummy buffer

  // gate new hlapi handshake until old parameters have all been popped
  assign hlapi_validi  = hlapi_valid & (bpar_q_lvl == '0);
  assign hlapi_accept  = hlapi_accepti & (bpar_q_lvl == '0);
  assign hlapi_alay_en = hlapi_valid & hlapi_accept;

  // linear read vm for bpar, discard output data, already captured in local fifo
  assign bf.base = '0;
  assign bf.len  = '1;
  npu_agu
    #(
      .R (1)
      )
  u_bpar_rd_inst
    (
     .clk        ( clk            ),
     .rst_a      ( rst_a          ),
     .soft_rst   ( 1'b0           ), // itnetionally tied to 0, no soft reset
     .in_valid   ( hlapi_validi   ),
     .in_accept  ( hlapi_accepti  ),
     .iter       ( hlapi_bnum     ),
     .offset     ( 16'h0001       ),
     .bf         ( bf             ),
     .ptr        ( hlapi_bptr     ),
     .out_valid  ( v_valid        ),
     .out_accept ( v_accept       ),
     .out_addr   ( vm_rd_cmd_addr )
    );

  
  //
  // Limit to buffer size
  //
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :LHS lvl_nxt, data_len, rd_ptr_nxt is less than RHS, which can be ignored
  assign vm_rd_cmd_valid = v_valid & (~lvl_r[5]);
  assign v_accept        = vm_rd_cmd_accept & (~lvl_r[5]);
  always_comb
  begin : lim_PROC
    lvl_en          = 1'b0;
    lvl_nxt         = lvl_r;
    if (v_valid & v_accept)
    begin
      lvl_en  = 1'b1;
      lvl_nxt = lvl_nxt + 1'b1;
    end
    if (bpar_pop_q)
    begin
      lvl_en  = 1'b1;
      lvl_nxt = lvl_nxt - {bpar_pop_q_num,2'b00};
    end    
  end : lim_PROC
  

  // Drive outputs
  // outputs: int_out_accept, bpar_out, bpar_q_lvl
  always_comb
  begin : out_PROC
    ixacc_t  [ACT_BREG_NUM-1:0] bpar_tmp;        // per channel parameter temporary
    logic    [3:0]              data_len;
    data_len   = wr_ptr_r[5:2] - rd_ptr_r;
    bpar_q_lvl = {2'd0,data_len};  // number in ixacc_t
    // output data is rotated fifo data in units of 512b
// spyglass disable_block W486 FLAT_504
//SMD: No overflow 
//SJ : npu_gtoa_bpar_rd will not exceed limit
    bpar_tmp = {fifo_data_r,fifo_data_r} >> {rd_ptr_r[4:2],9'h0};
// spyglass enable_block W486 FLAT_504
    bpar_out  = '0;
    if (hlapi_alay_r)
    begin
      // two sets of data
      for (int p = 0; p < ACT_BREG_NUM/2; p++)
      begin
        if (p < bpar_pop_q_num[3:1])
        begin
          bpar_out[p]                  = bpar_tmp[p];
          bpar_out[p + ACT_BREG_NUM/2] = bpar_tmp[p + bpar_pop_q_num[3:1]];
        end
      end
    end
    else
    begin
      bpar_out = bpar_tmp;
    end
  end : out_PROC
  
  // next state
  // outputs: rd_ptr_nxt, wr_ptr_nxt, fifo_data_en
  assign wr_ptr_nxt = wr_ptr_r + 'd1;
  assign rd_ptr_nxt = rd_ptr_r + bpar_pop_q_num;
  always_comb
  begin : nxt_PROC
    fifo_data_en  = '0;
    fifo_data_en[wr_ptr_r[4:0]] = vm_rd_rvalid;
  end : nxt_PROC
// spyglass enable_block W164a
  
  // register
  // outputs: rd_ptr_r, wr_ptr_r, fifo_data_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1) 
    begin
      rd_ptr_r    <= 8'h0;
      wr_ptr_r    <= 8'h0;
      fifo_data_r <= '0;
      lvl_r       <= '0;
      hlapi_alay_r <= 1'b0;
    end
    else 
    begin 
      if (vm_rd_rvalid) begin
        wr_ptr_r <= wr_ptr_nxt;        
      end
      for (int i = 0; i < 32; i++)
      begin
        if (fifo_data_en[i]) begin
          fifo_data_r[i] <= vm_rd_rdata;
        end
      end
      if (bpar_pop_q) begin
        rd_ptr_r <= rd_ptr_nxt;
      end
      if (lvl_en)
      begin
        lvl_r <= lvl_nxt;
      end
      if (hlapi_alay_en)
      begin
        hlapi_alay_r <= hlapi_alay;
      end
    end
  end : reg_PROC

`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_notempty;
  @(posedge clk) disable iff (rst_a !== 1'b0) bpar_pop_q |-> bpar_pop_q_num <= bpar_q_lvl;
  endproperty : prop_notempty
  a_ackempty: assert property (prop_notempty) else $fatal(1, "Error: parameter queue underflow");
`endif
  
endmodule : npu_gtoa_bpar_rd
