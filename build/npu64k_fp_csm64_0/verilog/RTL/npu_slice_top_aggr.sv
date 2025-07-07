
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



module npu_slice_top_aggr
  import npu_types::*;
  import npu_ecc_types::*;
  (
  input  logic              dmi_clk_req_sync, // clock request from AXI DMI
  input  logic              clk_en_sync,      // synchronized clock enable
  input  logic              dbg_cmdval_sync,
  input  logic              dbg_cmdack,
  input  logic              dbg_rspval,
  input  logic       [31:0] dbg_rdata,
  input  logic              debug_reset,
  input  logic       [36:0] dbg_pack_a,

  output logic              clk_en_eff,       // effective clock enable
  output logic              dbg_cmdval,
  output logic       [31:0] dbg_address,
  output logic       [1:0]  dbg_cmd,
  output logic       [31:0] dbg_wdata,
  output logic       [31:0] dbg_resp, 

  input  logic              clk,
  input  logic              rst_sync
);
  // local types
  typedef enum logic [1:0] {dbg_state_idle_e, dbg_state_val_e, dbg_state_resp_e} dbg_state_t;

  dbg_state_t        dbg_state_r;      // BVCI state
  dbg_state_t        dbg_state_nxt;
  logic              dbg_state_en;
  logic              dbg_cmd_en;       // BVCI command register
  logic              dbg_cmdval_r;
  logic       [36:0] dbg_cmd_r;
  logic              dbg_rsp_en;
  logic       [31:0] dbg_rsp_r;        // BVCI response register

  assign dbg_cmdval  = '0;
  assign dbg_address = '0;
  assign dbg_cmd     = '0;
  assign dbg_wdata   = '0;
  assign dbg_resp    = '0;


  assign clk_en_eff = dmi_clk_req_sync | clk_en_sync;

endmodule : npu_slice_top_aggr
