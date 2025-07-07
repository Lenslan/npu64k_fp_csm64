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
// convolution stash module padding load module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_vm_read.sv npu_conv_types.sv npu_conv_stash_pad_load.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_vm_read.sv ../npu_conv_types.sv ../npu_conv_stash_pad_load.sv"
//
 
`include "npu_defines.v"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_conv_macros.svh"


module npu_conv_stash_pad_load
  import npu_types::*;
  import npu_conv_types::*;
  (
   // Clock and reset
   input  logic          clk,                          // Clock, all logic clocked at posedge
   input  logic          rst_a,                        // Asynchronous reset, active high
   // HLAPI interface
   input  logic          hlapi_valid,                  // Request new HLAPI start
   output logic          hlapi_accept,                 // Acknowledge new HLAPI start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  conv_hlapi_i_t hlapi_i,                      // HLAPI parameters
// spyglass enable_block W240
   // VM load interface
   `VMRMST(1,vm_rd_),                                  // 1 bank VM padding read
   // Padding output interface
   output logic          pad_valid,                    // Padding information is valid
   input  logic          pad_accept,                   // Padding information is accepted
   output ixpix_t [3:0]  pad_data                      // Padding information
   );
  // local wires
  logic          cf_en;           // config register enable
  logic    [1:0] inuml2;          // log2 of number of blocks per iteration
  logic    [2:0] cf_inum_r;       // number of blocks per iteration
  logic    [2:0] cf_inum_nxt;     // number of blocks per iteration
  offset_t [3:0] iter;            // iterator over padding
  offset_t [3:0] offset;          // AGU offsets
  logic          out_valid;       // valid VM read data
  logic          out_accept;      // accept VM read data
  ixpix_t        out_ixpix;       // VM read data
  logic          pad_en;          // pad queue enable
  logic    [3:0] pad_lvl_r;       // level of pad output register
  ixpix_t  [7:0] pad_r;           // padding values
  logic    [3:0] pad_lvl_nxt;     // level of pad output register next state
  ixpix_t  [7:0] pad_nxt;         // padding values next state
  logic          busy;            // busy, so cannot accept new command
  logic          rdbusy;          // VM read is busy
  logic          i_hlapi_valid;   // gated HLAPI flow control
  logic          i_hlapi_accept;
  logic          dw_dbl;          // DW convolution enable fm16
  buf_t          bf;
  
  
  assign dw_dbl       = (hlapi_i.fm_cfg==fm_cfg_16b_e ||
                         hlapi_i.fm_cfg==fm_cfg_fp16_e ||
                         hlapi_i.fm_cfg==fm_cfg_bf16_e) && 
                        (hlapi_i.conv_mode == `NINO(conv_mode_3x3dws1) || 
                         hlapi_i.conv_mode == `NINO(conv_mode_8x1dws1) ||
                         hlapi_i.conv_mode == `NINO(conv_mode_2x3dws2) || 
                         hlapi_i.conv_mode == `NINO(conv_mode_3x3dws1dl2));

  //
  // iterator
  //
  assign i_hlapi_valid = hlapi_valid & (~busy);
  assign hlapi_accept  = i_hlapi_accept & (~busy);
  assign inuml2      = (hlapi_i.iter[6][1] || dw_dbl) ? (hlapi_i.conv_mode == `DINO(conv_mode_1x1) ? 2'd2 : 2'd1) : (hlapi_i.conv_mode == `DINO(conv_mode_1x1) ? 2'd1 : 2'd0);
  assign cf_inum_nxt = 1'b1<<inuml2;
  assign iter[0]     = hlapi_i.iter[0]; // grp
  assign iter[1]     = hlapi_i.iter[1]; // no
  assign iter[2]     = hlapi_i.iter[2]; // ni
  assign iter[3]     = {13'b0, cf_inum_nxt};     // inn loop, i16, i32 or 164
  assign offset[0] = 16'h1;
  assign offset[1] = 16'h1 - (hlapi_i.iter[2]<<inuml2);
  assign offset[2] = 16'h1;
  assign offset[3] = 16'h1;
  
  //
  // store some configuration parameters
  //
  assign cf_en = hlapi_valid & hlapi_accept;
  // outputs: cf_inum_r
  always_ff @(posedge clk or posedge rst_a)
  begin : cf_reg_PROC
    if (rst_a == 1'b1)
    begin
      cf_inum_r <= 1'b0;
    end
    else if (cf_en)
    begin
      cf_inum_r <= cf_inum_nxt;
    end
  end : cf_reg_PROC
  
  
  //
  // Read values from VM: [grp][no][ni][inum]
  //
  assign bf.base = '0;
  assign bf.len  = '1;
  npu_vm_read
    #(
      .D ( 2 ),
      .R ( 4 )
      )
  u_rd_inst
    (
     .clk        ( clk             ),
     .rst_a      ( rst_a           ),
     .soft_rst   ( 1'b0            ),
     .busy       ( rdbusy          ),
     .in_valid   ( i_hlapi_valid   ),
     .in_accept  ( i_hlapi_accept  ),
     .iter       ( iter            ),
     .offset     ( offset          ),
     .bf         ( bf              ),
     .ptr        ( hlapi_i.pad_ptr ),
     `VMRINST_S(1,vm_rd_,vm_rd_,0),
     .out_valid  ( out_valid       ),
     .out_accept ( out_accept      ),
     .out_ixpix  ( out_ixpix       )
   );
  
  //
  // Accept VM data into padding register
  //
  assign pad_valid = pad_lvl_r >= {1'b0,cf_inum_r};
  assign pad_data  = pad_r;
  // outputs: pad_en, pad_lvl_nxt, pad_nxt, out_accept
  always_comb
  begin : pad_nxt_PROC
    // default outputs
    pad_en      = 1'b0;
    pad_lvl_nxt = pad_lvl_r;
    pad_nxt     = pad_r;
    out_accept  = 1'b0;
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow and Ignore pad_lvl_nxt
    if (pad_valid & pad_accept)
    begin
      // pop data from queue
      pad_en      = 1'b1;
      pad_lvl_nxt = pad_lvl_r - cf_inum_r;
      pad_nxt     = pad_r >> {cf_inum_r,7'h00}; // shift in units of 128b
    end
// spyglass enable_block W164a
// spyglass disable_block ImproperRangeIndex-ML
//SMD:Improper range idex
//SJ :pad_lvl_nxt less than max range of pad_nxt, won't influence result and ignore
    if (out_valid && (pad_lvl_nxt < 4'd8))
    begin
      // add data to queue
      out_accept           = 1'b1;
      pad_en               = 1'b1;
      pad_nxt[pad_lvl_nxt] = out_ixpix;
      pad_lvl_nxt          = pad_lvl_nxt + 4'd1;
    end
// spyglass enable_block ImproperRangeIndex-ML
  end : pad_nxt_PROC

  // output registers
  // outputs: pad_lvl_r, pad_r
  always_ff @(posedge clk or posedge rst_a)
  begin : pad_reg_PROC
    if (rst_a == 1'b1)
    begin
      pad_r     <= '0;
      pad_lvl_r <= '0;
    end
    else if (pad_en)
    begin
      pad_r     <= pad_nxt;
      pad_lvl_r <= pad_lvl_nxt;
    end
  end : pad_reg_PROC

  assign busy = rdbusy || (pad_lvl_r != '0);
  
endmodule : npu_conv_stash_pad_load
