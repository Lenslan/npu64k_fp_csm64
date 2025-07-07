/*
 * Copyright (C) 2022 Synopsys, Inc. All rights reserved.
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
// File defining the npu fabric safety monitor
//

`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
module npu_grp_sfty_monitor
  import npu_types::*;
  (
  // read command channel
  input  logic                        sfty_cfg_axi_arvalid, // read command valid
  output logic                        sfty_cfg_axi_arready, // read command accept
  input  logic          [1-1:0]  sfty_cfg_axi_arid,    // read command ID
  input  logic          [1-1:0] sfty_cfg_axi_aruser,  // read command user field
  input  logic          [NPU_AXI_ADDR_W-1:0]   sfty_cfg_axi_araddr  ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_arcache ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_arprot  ,      // read command
  input  logic          [1-1:0]         sfty_cfg_axi_arlock  ,      // read command
  input  logic          [1:0]         sfty_cfg_axi_arburst ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_arlen   ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_arsize  ,      // read command
  input  logic          [NPU_AXI_REGION_W-1:0]         sfty_cfg_axi_arregion,      // read command
  // read data channel
  output logic                        sfty_cfg_axi_rvalid,  // read data valid
  input  logic                        sfty_cfg_axi_rready,  // read data accept
  output logic          [1-1:0]  sfty_cfg_axi_rid,     // read data id
  output logic          [32-1:0]   sfty_cfg_axi_rdata,   // read data
  output logic          [1:0]         sfty_cfg_axi_rresp,   // read response
  output logic          [1-1:0]  sfty_cfg_axi_ruser,   // read data user field
  output logic                        sfty_cfg_axi_rlast,   // read last
  // write command channel
  input  logic                        sfty_cfg_axi_awvalid, // write command valid
  output logic                        sfty_cfg_axi_awready, // write command accept
  input  logic          [1-1:0]  sfty_cfg_axi_awid,    // write command ID
  input  logic          [1-1:0] sfty_cfg_axi_awuser,  // write command user field
  input  logic          [NPU_AXI_ADDR_W-1:0]   sfty_cfg_axi_awaddr  ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_awcache ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_awprot  ,      // read command
  input  logic          [1-1:0]         sfty_cfg_axi_awlock  ,      // read command
  input  logic          [1:0]         sfty_cfg_axi_awburst ,      // read command
  input  logic          [3:0]         sfty_cfg_axi_awlen   ,      // read command
  input  logic          [2:0]         sfty_cfg_axi_awsize  ,      // read command
  input  logic          [NPU_AXI_REGION_W-1:0]         sfty_cfg_axi_awregion,      // read command
  // write data channel
  input  logic                        sfty_cfg_axi_wvalid,  // write data valid
  output logic                        sfty_cfg_axi_wready,  // write data accept
  input  logic          [32-1:0]   sfty_cfg_axi_wdata,   // write data
  input  logic          [32/8-1:0] sfty_cfg_axi_wstrb,   // write data strobe
  input  logic          [1-1:0]  sfty_cfg_axi_wuser,   // write data user field
  input  logic                        sfty_cfg_axi_wlast,   // write data last
  // write response channel
  output logic                        sfty_cfg_axi_bvalid,  // write response valid
  input  logic                        sfty_cfg_axi_bready,  // write response accept
  output logic          [1-1:0]  sfty_cfg_axi_bid,     // write response id
  output logic          [1-1:0]  sfty_cfg_axi_buser,   // read data user field
  output logic          [1:0]         sfty_cfg_axi_bresp,   // write response,
   // dbank mem ecc
   output logic                        dbnk_ecc_en,
   output logic                        dbnk_scrub_en,
   output logic                        dbnk_init,
   input  logic                        dbnk_init_done0,
   input  logic                        dbnk_sbe0,
   input  logic                        dbnk_dbe0, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done1,
   input  logic                        dbnk_sbe1,
   input  logic                        dbnk_dbe1, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done2,
   input  logic                        dbnk_sbe2,
   input  logic                        dbnk_dbe2, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done3,
   input  logic                        dbnk_sbe3,
   input  logic                        dbnk_dbe3, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done4,
   input  logic                        dbnk_sbe4,
   input  logic                        dbnk_dbe4, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done5,
   input  logic                        dbnk_sbe5,
   input  logic                        dbnk_dbe5, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done6,
   input  logic                        dbnk_sbe6,
   input  logic                        dbnk_dbe6, // fatal error consist of dbe/addr/unknown
   input  logic                        dbnk_init_done7,
   input  logic                        dbnk_sbe7,
   input  logic                        dbnk_dbe7, // fatal error consist of dbe/addr/unknown
   output logic                        scm_dbank_ecc_irq,
   // report dbank sbe/dbe: to NPX top
   output logic                        scm_dbank_sbe,
   output logic                        scm_dbank_dbe,
   // System interface
   input  logic                        clk,      // always-on clock
   input  logic                        rst_a     // asynchronous reset, active high, synchronous deassertion
  );
logic       dbnk_dbe_aggr;
logic       dbnk_sbe_aggr;
logic [31:0] npu_grp_dbank_ecc_ctrl_r;

// dbank
logic       dbnk_dbe0_r;
logic       dbnk_sbe0_r;
logic       dbnk_dbe1_r;
logic       dbnk_sbe1_r;
logic       dbnk_dbe2_r;
logic       dbnk_sbe2_r;
logic       dbnk_dbe3_r;
logic       dbnk_sbe3_r;
logic       dbnk_dbe4_r;
logic       dbnk_sbe4_r;
logic       dbnk_dbe5_r;
logic       dbnk_sbe5_r;
logic       dbnk_dbe6_r;
logic       dbnk_sbe6_r;
logic       dbnk_dbe7_r;
logic       dbnk_sbe7_r;
logic       dbnk_dbe_r;
logic       dbnk_sbe_r;
logic dbnk_init_r;
logic dbnk_init_done;
logic [7:0] dbnk_num;
logic [7:0] dbnk_num_r;

assign dbnk_ecc_en    = npu_grp_dbank_ecc_ctrl_r[0];
assign dbnk_scrub_en  = npu_grp_dbank_ecc_ctrl_r[1];
assign dbnk_init      = ({dbnk_init_r,npu_grp_dbank_ecc_ctrl_r[2]} == 2'b01); // pulse
assign dbnk_init_done = dbnk_init_done0
                        & dbnk_init_done1
                        & dbnk_init_done2
                        & dbnk_init_done3
                        & dbnk_init_done4
                        & dbnk_init_done5
                        & dbnk_init_done6
                        & dbnk_init_done7
                        ;
assign dbnk_num       = 
                        (dbnk_dbe0_r)? 8'd0:
                        (dbnk_dbe1_r)? 8'd1:
                        (dbnk_dbe2_r)? 8'd2:
                        (dbnk_dbe3_r)? 8'd3:
                        (dbnk_dbe4_r)? 8'd4:
                        (dbnk_dbe5_r)? 8'd5:
                        (dbnk_dbe6_r)? 8'd6:
                        (dbnk_dbe7_r)? 8'd7:
                        '0;

assign dbnk_dbe_aggr = 0
                    | dbnk_dbe0_r
                    | dbnk_dbe1_r
                    | dbnk_dbe2_r
                    | dbnk_dbe3_r
                    | dbnk_dbe4_r
                    | dbnk_dbe5_r
                    | dbnk_dbe6_r
                    | dbnk_dbe7_r
                      ;

assign dbnk_sbe_aggr = 0
                    | dbnk_sbe0_r
                    | dbnk_sbe1_r
                    | dbnk_sbe2_r
                    | dbnk_sbe3_r
                    | dbnk_sbe4_r
                    | dbnk_sbe5_r
                    | dbnk_sbe6_r
                    | dbnk_sbe7_r
                      ;
always @(posedge clk or posedge rst_a)
begin: dbnk_reg_PROC
  if (rst_a == 1)
  begin
    dbnk_dbe0_r <= 1'b0;
    dbnk_sbe0_r <= 1'b0;
    dbnk_dbe1_r <= 1'b0;
    dbnk_sbe1_r <= 1'b0;
    dbnk_dbe2_r <= 1'b0;
    dbnk_sbe2_r <= 1'b0;
    dbnk_dbe3_r <= 1'b0;
    dbnk_sbe3_r <= 1'b0;
    dbnk_dbe4_r <= 1'b0;
    dbnk_sbe4_r <= 1'b0;
    dbnk_dbe5_r <= 1'b0;
    dbnk_sbe5_r <= 1'b0;
    dbnk_dbe6_r <= 1'b0;
    dbnk_sbe6_r <= 1'b0;
    dbnk_dbe7_r <= 1'b0;
    dbnk_sbe7_r <= 1'b0;
    dbnk_dbe_r     <= 1'b0;
    dbnk_sbe_r     <= 1'b0;     
    dbnk_init_r    <= 1'b0;
    dbnk_num_r     <= '0;
  end  
  else
  begin
    dbnk_dbe0_r <= dbnk_dbe0;
    dbnk_sbe0_r <= dbnk_sbe0;
    dbnk_dbe1_r <= dbnk_dbe1;
    dbnk_sbe1_r <= dbnk_sbe1;
    dbnk_dbe2_r <= dbnk_dbe2;
    dbnk_sbe2_r <= dbnk_sbe2;
    dbnk_dbe3_r <= dbnk_dbe3;
    dbnk_sbe3_r <= dbnk_sbe3;
    dbnk_dbe4_r <= dbnk_dbe4;
    dbnk_sbe4_r <= dbnk_sbe4;
    dbnk_dbe5_r <= dbnk_dbe5;
    dbnk_sbe5_r <= dbnk_sbe5;
    dbnk_dbe6_r <= dbnk_dbe6;
    dbnk_sbe6_r <= dbnk_sbe6;
    dbnk_dbe7_r <= dbnk_dbe7;
    dbnk_sbe7_r <= dbnk_sbe7;
    dbnk_dbe_r     <= dbnk_dbe_aggr;
    dbnk_sbe_r     <= dbnk_sbe_aggr;
    dbnk_init_r    <= npu_grp_dbank_ecc_ctrl_r[2];
    dbnk_num_r     <= dbnk_num;
  end  
end
assign scm_dbank_dbe = dbnk_dbe_r;
assign scm_dbank_sbe = dbnk_sbe_r;

assign scm_dbank_ecc_irq = dbnk_ecc_en & npu_grp_dbank_ecc_ctrl_r[16];      


npu_grp_sfty_monitor_regs u_npu_grp_sfty_monitor_regs (
 // System interface
    `AXIINST_EXT(sfty_cfg_axi_,sfty_cfg_axi_),
    .npu_grp_dbank_ecc_ctrl_r              (npu_grp_dbank_ecc_ctrl_r),
 // dbnk ctrl & status                     
    .dbnk_dbe                              (dbnk_dbe_r),
    .dbnk_sbe                              (dbnk_sbe_r),
    .dbnk_init_done                        (dbnk_init_done),
    .dbnk_num                              (dbnk_num_r),
 // Clock, Reset
    .rst_a                                 (rst_a),
    .clk                                   (clk)
);

endmodule

