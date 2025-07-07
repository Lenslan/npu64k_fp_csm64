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
// convolution stash module scalar AGU computing address of start of column
//  vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv npu_conv_types.sv npu_conv_stash_scalar.sv
//  analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../npu_conv_types.sv ../npu_conv_stash_scalar.sv"
//

`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_conv_macros.svh"

module npu_conv_stash_scalar
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
   // Quadrant input interface
   input  logic          quad_valid,                   // Quadrant information is valid
   output logic          quad_accept,                  // Quadrant information is accepted
   input  quadrant_t     quad_data,                    // Quadrant information
   // Scalar output interface
   output logic          scalar_valid,                 // Scalar information is valid
   input  logic          scalar_accept,                // Scalar information is accepted
   output vm_scalar_t    scalar_data                   // Scalar information
   );
  // local wires
  logic                it_req;          // iterator output valid
  logic                it_ack;          // iterator output acknowledge
  logic          [4:0] it_first;        // iterator first flags
  logic          [4:0] it_last;         // iterator last flags
  logic                it_vald;         // iterator last/first flags valid
  logic                cf_en;           // enable parameters
  buf_t                cf_buf_r;        // VM buffer
  offset_t             cf_coffset_r;    // column pointer offset
  offset_t             cf_cstride_r;    // column index offset
  offset_t             cf_coffset_nxt;  // column pointer offset next
  offset_t             cf_cstride_nxt;  // column index offset next
  logic                str2;            // stride2 convolution mode
  logic                up_en;           // enable running data
  logic                keep_en;         // enable first channel pointer
  vm_addr_t            ptr_r;           // running VM pointer
  vm_addr_t            ptr_nxt;         // running VM pointer, new value
  vm_addr_t            ptr_keep_r;      // pointer to first input channel in group
  offset_t       [2:0] padpos_r;        // running padding position
  offset_t       [2:0] padpos_nxt;      // running padding position
  
  
  //
  // Iterator over [grp][no][ni][qd][col]
  //
  npu_iterator
    #(
      .N ( 5 )
      )
  u_iter_inst
    (
   .clk      ( clk               ),
   .rst_a    ( rst_a             ),
   .soft_rst ( 1'b0              ),
   .in_req   ( hlapi_valid       ),
   .in_ack   ( hlapi_accept      ),
   .in_shp   ( hlapi_i.iter[4:0] ),
   .it_req   ( it_req            ),
   .it_ack   ( it_ack            ),
   .it_first ( it_first          ),
   .it_last  ( it_last           ),
   .it_vald  ( it_vald           )
   );

  //
  // Update state
  //
  // outputs: cf_en, up_en, keep_en, quad_accept, scalar_valid, it_ack
  always_comb
  begin : state_nxt_PROC
    vm_addr_t ptr;
    vm_inc_t  incrm;
    buf_t     bf;
    // defaults
    cf_en        = 1'b0;
    up_en        = 1'b0;
    keep_en      = 1'b0;
    it_ack       = 1'b0;
    quad_accept  = 1'b0;
    scalar_valid = 1'b0;
    incrm        = '0;
    padpos_nxt   = hlapi_i.fm_padpos;
    bf.base      = hlapi_i.fm_buf_base;
    bf.len       = hlapi_i.fm_buf_len;
    ptr          = hlapi_i.fm_ptr;
    if (hlapi_valid && hlapi_accept)
    begin
      // initialize registers from HLAPI parameters
      cf_en      = 1'b1;
      up_en      = 1'b1;
      keep_en    = 1'b1;
    end
    else if (it_req) 
    begin
      offset_t [2:0] pad_delta; // padding offset
      ptr          = ptr_r;
      bf           = cf_buf_r;
      padpos_nxt   = padpos_r;
      pad_delta    = quad_data.pdoffs;
      casez (it_last)
      5'b11111:
        begin
          // done
          scalar_valid = quad_valid;
          quad_accept  = scalar_accept;
          it_ack       = quad_valid & scalar_accept;
        end
      5'b11110:
        begin
          // next group
          scalar_valid = quad_valid;
          quad_accept  = scalar_accept;
          keep_en      = quad_valid & scalar_accept;
          up_en        = quad_valid & scalar_accept;
          it_ack       = quad_valid & scalar_accept;
          incrm        = quad_data.doffs;
        end
      5'b1110?:
        begin
          // next output channel
          ptr          = ptr_keep_r; // reset VM point to first input channel in group
          scalar_valid = quad_valid;
          quad_accept  = scalar_accept;
          up_en        = quad_valid & scalar_accept;
          it_ack       = quad_valid & scalar_accept;
        end
      5'b110??,
      5'b10???:
        begin
          // next input channel or next quadrant
          scalar_valid = quad_valid;
          quad_accept  = scalar_accept;
          up_en        = quad_valid & scalar_accept;
          //incrm        = hlapi_i.quad_data[3].doffs; //FIXME: to be updated for mqd
          incrm        = quad_data.doffs;
          it_ack       = quad_valid & scalar_accept;
        end
      default:
        begin
          // next column
          scalar_valid = 1'b1;
          up_en        = scalar_accept;
          incrm        = cf_coffset_r;
          it_ack       = scalar_accept;
          pad_delta[0] = cf_cstride_r;
          pad_delta[1] = 0;
          pad_delta[2] = 0;
        end
      endcase // casez (it_last)
      // update padding
      for (int d = 0; d < 3; d++)
      begin
        padpos_nxt[d] += pad_delta[d];
      end
    end
    // increment and wrap the VM pointer
    ptr_nxt  = incr_vm(ptr, incrm, bf);
  end : state_nxt_PROC

  // state registers
  assign str2           = hlapi_i.conv_mode == `NINO(conv_mode_2x1g2s2) || hlapi_i.conv_mode == `NINO(conv_mode_2x1s2) || hlapi_i.conv_mode == `NINO(conv_mode_2x3dws2);
  assign cf_coffset_nxt = str2 ? hlapi_i.fm_offsets [FMO_W]*2*VSIZE : hlapi_i.fm_offsets [FMO_W]*VSIZE;
  assign cf_cstride_nxt = str2 ? hlapi_i.fm_poffsets[FMO_W]*2*VSIZE : hlapi_i.fm_poffsets[FMO_W]*VSIZE;
  // outputs: cf_buf_r, cf_coffset_r, cf_cstride_r, padpos_r, ptr_r, ptr_keep_r
  always_ff @(posedge clk or posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      cf_buf_r        <= {BUF_SZ{1'b0}};
      cf_coffset_r    <= '0;
      cf_cstride_r    <= '0;
      ptr_r           <= '0;
      ptr_keep_r      <= '0;
      padpos_r        <= '0;
    end
    else
    begin
      if (cf_en)
      begin
        cf_buf_r.base <= hlapi_i.fm_buf_base;
        cf_buf_r.len  <= hlapi_i.fm_buf_len;
        cf_coffset_r  <= cf_coffset_nxt;
        cf_cstride_r  <= cf_cstride_nxt;
      end
      if (up_en)
      begin
        padpos_r      <= padpos_nxt;
        ptr_r         <= ptr_nxt;
      end
      if (keep_en)
      begin
        ptr_keep_r    <= ptr_nxt;
      end
    end
  end : state_reg_PROC

  // assign to outputs
  assign scalar_data.ptr  = ptr_r;
  assign scalar_data.ppos = padpos_r;
  
endmodule : npu_conv_stash_scalar
