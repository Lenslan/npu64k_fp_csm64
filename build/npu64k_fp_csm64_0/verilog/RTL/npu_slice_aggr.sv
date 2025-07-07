
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

// NPU toplevel
// vcs -sverilog +define+DUMMY_SLICE -f ../../shared/RTL/npu_shared_manifest ../../npu_slice/RTL/npu_slice.sv npu_slice_top.sv npu_cln_wrap.sv npu_cln_group.sv npu_cln_1p5.sv npu_stu_top.sv dummy_modules/npuarc_hs_cluster_top.sv npu_l2arc_group.sv npu_debug_port.v  npu_jtag_port.v  npu_tap_controller.v npu_core.sv npu_top.sv

`include "npu_macros.svh"

`include "npu_defines.v"
`include "npu_axi_macros.svh"


module npu_slice_aggr 
  import npu_types::*;
  import npu_ecc_types::*;
#(
  parameter int NUM_TRACE_SRC = 5
) (
  input  logic [7:0]                      clusternum,
  input  logic [7:0]                      arcnum,
  input  logic                            rst_trace_sync,
  input  logic [NUM_TRACE_SRC-1:0]        trace_valid_in,
  output logic [NUM_TRACE_SRC-1:0]        trace_accept_in,
  input  logic                            trace_valid_out,
  input  logic [31:0]                     trace_id_out,

  output logic                            i_swe_val ,
  output logic [32:0]                     i_swe_data,
  output logic [7:0]                      i_swe_ext ,
  `STRMST(stro_,vyixacc_t),
  `STRSLV(i_stro_,vyixacc_t),
  input  logic                            rst_fifo_sync,
  input  logic                            clk

);
  logic [NUM_TRACE_SRC-1:0]   trace_valid_d1;
  logic [NUM_TRACE_SRC-1:0]   trace_valid_d2;
  logic [NUM_TRACE_SRC-1:0]   trace_valid_d3;
  logic [NUM_TRACE_SRC-1:0]   trace_valid_d4;

`ifdef STR_FIFO_INJECT_STALL
  logic [6:0] stall_flag;  //up to 128 cycles

  //`VPOST_OFF
  always_ff @(posedge clk or posedge rst_fifo_sync)
  begin : stall_flag_PROC
    if (rst_fifo_sync ==1'b1) begin
      stall_flag        <= $random;
    end
    else begin
      if ((stall_flag == '0) && stro_str_accept) begin
        stall_flag        <= $random;
      end
      else if (i_stro_str_valid && (stall_flag != '0)) begin
        stall_flag        <= stall_flag - 'b1;
      end
    end
  end : stall_flag_PROC
  //`VPOST_ON

  always_comb
  begin : str_fifo_inject_stall_PROC
    stro_str_valid    =   (stall_flag != '0) ? 1'b0 : i_stro_str_valid;
    i_stro_str_accept =   (stall_flag != '0) ? 1'b0 : stro_str_accept;
  end : str_fifo_inject_stall_PROC
`else
  assign stro_str_valid    =   i_stro_str_valid;
  assign i_stro_str_accept =   stro_str_accept;
`endif
  assign stro_str_data     =   i_stro_str_data;


  assign i_swe_ext  = {clusternum[2:0],arcnum[4:0]};
  assign i_swe_val  = trace_valid_out;
  // the 33th bit is the identifier for start/end
  // the [31:0] bits are the payload
  assign i_swe_data = {trace_id_out[31],1'b0,trace_id_out[30:0]};
  // trace accept: always accept after valid is asserted for 5 cycles
  // SWE will be dropped if skid buffer is invalid
  assign trace_accept_in = trace_valid_in & trace_valid_d4 & trace_valid_d3 & trace_valid_d2 & trace_valid_d1;

  // delayed valid
  //`VPOST_OFF
  always_ff @(posedge clk or posedge rst_trace_sync)
  begin : trace_dly_PROC
    if (rst_trace_sync ==1'b1) begin
      trace_valid_d1      <= '0;
      trace_valid_d2      <= '0;
      trace_valid_d3      <= '0;
      trace_valid_d4      <= '0;
    end
    else begin
      trace_valid_d1      <= trace_valid_in;
      trace_valid_d2      <= trace_valid_d1;
      trace_valid_d3      <= trace_valid_d2;
      trace_valid_d4      <= trace_valid_d3;
    end
  end : trace_dly_PROC
  //`VPOST_ON


endmodule : npu_slice_aggr
