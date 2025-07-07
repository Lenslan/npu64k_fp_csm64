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
// convolution coefficient fetching module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_vm_read.sv npu_conv_types.sv npu_conv_coef_pipe.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL" [list ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_vm_read.sv ../npu_conv_types.sv ../npu_conv_coef_pipe.sv]
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_conv_macros.svh"

`define SV_COUNTONES_EMULATE 1

module npu_conv_coef_pipe
  import npu_types::*;
  import npu_conv_types::*;
  #(
    parameter int IDX = 0                   // padding index
  )
  (
   //
   // Clock and reset
   //
   input  logic                   clk,                          // Clock, all logic clocked at posedge
   input  logic                   rst_a,                        // Asynchronous reset, active high
   input  logic                   soft_rst,                     // Soft-reset decoding pipe
   //
   // HLAPI interface
   //
   input  logic                   in_valid,                     // Request new HLAPI start
   output logic                   in_accept,                    // Acknowledge new HLAPI start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  conv_hlapi_i_t          hlapi_i,                      // HLAPI parameters
// spyglass enable_block W240
   input  vm_addr_t               in_ptr,                       // Pointer into buffer
   input  logic                   cf_dw3,                       // if true then depthwise
   input  logic                   cf_4b,                        // if true then 4b feature-map
   input  logic          [4:0]    cf_bsmax,                     // worst-case block size to pop
   input  coef_mode_t             cf_mode,                      // compression mode
   input  offset_t                cf_padlim,                    // pad limit
   //
   // External interfaces
   //
   `VMRMST(1,vm_rd_),                                           // 1 bank VM feature-map read
   //
   // Block of decoded coefficients
   //
   output logic                   coef_valid,                   // Coefficient block valid
   input  logic                   coef_accept,                  // Coefficient block accept
   input  logic          [3:0]    coef_padlast,                 // Pad position last bits
   input  logic                   coef_zp,                      // If true then decode a block of zero-points instead of coefficients
   output coef_atom_t             coef_data                     // Decoded coefficients
   );
  //
  // Local parameters
  //
  localparam int QS = 2*20+8; // queue size = 2*worst-case decode block - 2 + ISIZE, worst-case =20B, round up to ISIZE
  //
  // Local wires
  //
  logic                 bank_valid;  // VM data valid
  logic                 bank_accept; // VM data accept
  ixpix_t               bank_data;   // VM data
  logic   [QS-1:0]      queue_en;    // queue enables
  pix_t   [QS-1:0]      queue_r;     // queue of bytes register
  pix_t   [QS-1:0]      queue_nxt;   // queue of bytes
  logic                 lvl_en;      // level register enable
  logic   [5:0]         lvl_r;       // number of elements in the queue register
  logic   [5:0]         lvl_nxt;     // number of elements in the queue next
  logic   [4:0]         bs;          // number of bytes in decoded block
  logic                 padpos_en;   // padding position enable
  offset_t              padpos_nxt;  // next padding position
  offset_t              padpos_nxt_a;  // next padding position
  offset_t              padpos_nxt_b;  // next padding position
  offset_t              padpos_r;    // padding position
  buf_t                 bf;


  //
  // Functions
  //
// spyglass disable_block W416 SelfDeterminedExpr-ML W164a
//SMD:Function return type width mismatch
//SJ :Int type $countones(b) return in some config and can be ignore
  function automatic logic [4:0] count1s(input logic [19:0] b);
`ifndef SV_COUNTONES_EMULATE
    return $countones(b);
`else

    logic      [20:0] b_ext;
    logic [2:0][2:0]  r;
    logic      [4:0]  res;
    r     = '0;
    res   = '0;
    b_ext = {1'b0,b};
    for (int i=0; i<3; i++)
      begin
      for (int j=0; j<7; j++)
        begin
        r[i] = r[i] + {2'b0,b_ext[i*7+j]};
        end
      end
    res    = {2'b0,r[0]} + {2'b0,r[1]} + {2'b0,r[2]};
    return res;
`endif
  endfunction : count1s
// spyglass enable_block W416 SelfDeterminedExpr-ML W164a

  //
  // VM read instance
  //
  assign bf.base = '0;
  assign bf.len  = '1;
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  npu_vm_read
    #(
      .D ( 6 ),
      .R ( 4 ),
      .F ( 0 )
      )
  u_vmr_inst
    (
     .clk        ( clk               ),
     .rst_a      ( rst_a             ),
     .soft_rst   ( soft_rst          ),
     .busy       (                   ), // intentionally unconnected
     .in_valid   ( in_valid          ),
     .in_accept  ( in_accept         ),
     .iter       ( hlapi_i.cf_iter   ),
     .offset     ( hlapi_i.cf_offset ),
     .bf         ( bf                ),
     .ptr        ( in_ptr            ),
     `VMRINST_S(1,vm_rd_,vm_rd_,0    ),
     .out_valid  ( bank_valid        ),
     .out_accept ( bank_accept       ),
     .out_ixpix  ( bank_data         )
   );
// spyglass enable_block W287b
  
  //
  // Queue of bytes, max decode block size is 16*(8+2)+2*8=176b=22B (sparse mode)
  //
  
  // decode and accept coefficients from queue
  // outputs: coef_valid, coef_data, bs

// spyglass disable_block ImproperRangeIndex-ML
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  always_comb
  begin : dec_PROC
    pix_t [17:0] dc;     // decompressed 8b values
    pix_t [19:0] d4;     // expanded 4b values
    logic [15:0] avail;  // avail bits
    int          j;
    logic [19:0] c1mask; // mask for count1s
    // default output
    coef_data = '0;
    dc        = '0;
    c1mask    = 20'b1100_0000_0000_0000_0000;
    for (int i = 0; i < 4; i++)
    begin
      coef_data.ctrla[2*i+0] = selafm0;
      coef_data.ctrla[2*i+1] = selafm1;
      coef_data.ctrlb[2*i+0] = selbfm2;
      coef_data.ctrlb[2*i+1] = selbfm3;
    end
    // prepare by decompressing 18 coefficients
    avail = queue_r[1:0];
    for (int i = 0; i < 16; i++)
    begin
      j         = count1s(c1mask);
      dc[i]     = queue_r[j];
      c1mask[i] = avail[i];
    end
    // spare compressed coefficients for DW modes
    j          = count1s(c1mask);
    dc[16]     = queue_r[j];
    c1mask[16] = 1'b1;
    j          = count1s(c1mask);
    dc[17]     = queue_r[j];
    // prepare sign extend 4b coefficients to 8b
    for (int i = 0; i < 10; i++)
    begin
      d4[2*i+0] = {{4{queue_r[i][3]}}, queue_r[i][3:0]};
      d4[2*i+1] = {{4{queue_r[i][7]}}, queue_r[i][7:4]};
    end
    // extract spare coefficients for DW modes
    c1mask    = 20'b1100_0000_0000_0000_0000;
    casez ({cf_mode,cf_4b})
    {coef_mode_compressed,1'b?}:
      begin
        // compressed 8b mode
        coef_data.spare  |= dc[17:16];
      end
    {coef_mode_uncompressed,1'b1}:
      begin
        // uncompressed 4b mode
        coef_data.spare |= d4[17:16];
      end    
    default: // {coef_mode_uncompressed,1'b0}:
      begin
        // uncompressed 8b mode
        coef_data.spare |= queue_r[17:16];
      end
    endcase // casez ({cf_mode,cf_4b})  
    // decode sparse control
    if (cf_mode == coef_mode_sparse)
    begin
      for (int b = 0; b < 2; b++)
      begin
        for (int p = 0; p < 4; p++)
        begin
          coef_data.ctrla[b*4+p] = coef_sela_t'(queue_r[b][p*2+:2]);
          coef_data.ctrlb[b*4+p] = coef_selb_t'(queue_r[b+2][p*2+:2]);
        end
      end
    end
    // drive non-spare coefficient outputs
    if (coef_zp)
    begin
      // decode a block of zero-points
      c1mask              |= 20'b1111_1111_1111_1111_0000;
      coef_data.coef      |= queue_r[15:0];
    end
    else
    begin
      // decode a block of coefficients
      casez ({cf_mode,cf_dw3,cf_4b})
      {coef_mode_sparse      ,1'b?,1'b0}: 
        begin
          // sparse 8b mode: 4+16=20B (no DW support)
          c1mask          |= 20'b1111_1111_1111_1111_1111;
          coef_data.coef  |= queue_r[19:4];
        end
      {coef_mode_sparse      ,1'b?,1'b1}: 
        begin
          // sparse 4b mode: 4+8=12B (no DW support)
          c1mask          |= 20'b1111_1111_1111_0000_0000;
          coef_data.coef  |= d4[19:4];
        end
      {coef_mode_compressed  ,1'b0,1'b?}: 
        begin
          // compressed, non-depthwise, 8b mode: (16*(8+1))/8=18B (4b not supported)
          // first two bytes have 16 'avail' bits
          c1mask          |= {2'b11,avail,2'b00};
          coef_data.coef  |= dc[15:0];
          coef_data.nav   |= {2'b0, ~avail};
        end
      {coef_mode_compressed  ,1'b1,1'b?}: 
        begin
          // compressed, 3x3depthwise, 8b mode: (16*(8+1)+2*8)/8=20B (4b not supported)
          c1mask          |= {2'b11,avail,2'b11};
          coef_data.coef  |= dc[15:0];
          coef_data.nav   |= {2'b0, ~avail};
        end
      {coef_mode_uncompressed,1'b1,1'b1}: 
        begin 
          // uncompressed, 3x3depthwise, 4b mode: (16*4+2*4)/8=9B 
          c1mask          |= 20'b1111_1111_1000_0000_0000;
          coef_data.coef  |= d4[15:0];
        end
      {coef_mode_uncompressed,1'b0,1'b1}: 
        begin
          // uncompressed, non-depthwise, 4b mode: (16*4)/8=8B
          c1mask          |= 20'b1111_1111_0000_0000_0000;
          coef_data.coef  |= d4[15:0];
        end
      {coef_mode_uncompressed,1'b1,1'b0}:
        begin 
          // uncompressed, 3x3depthwise, 8b mode: (16*8+2*8)/8=18B
          c1mask          |= 20'b1111_1111_1111_1111_1100;
          coef_data.coef  |= queue_r[15:0];
        end
      default:
        begin
          // uncompressed, non-depthwise, 8b mode: (16*8)/8=16B
          c1mask          |= 20'b1111_1111_1111_1111_0000;
          coef_data.coef  |= queue_r[15:0];
        end
      endcase // casez ({cf_mode,cf_dw3,cf_4b})
    end // else: !if(coef_zp)
    // count the number of needed bytes
    bs = count1s(c1mask);
    // check if accept from queue, optimized for speed
    // spyglass disable_block W362
    //SMD:Width mismatch
    //SJ :No overflow and ignore
    coef_valid = (lvl_r >= (coef_zp ? 'h10 : cf_bsmax));
    // spyglass enable_block W362
    // padding for matrix*matrix mode
    if ((cf_mode == coef_mode_fm) && (padpos_r > cf_padlim))
    begin
      coef_data = '0;
    end
  end : dec_PROC
// spyglass enable_block SelfDeterminedExpr-ML
  // spyglass enable_block ImproperRangeIndex-ML  

  // accept new data input queue
  assign bank_accept = lvl_r <= (QS-16);
  
  // update the queue state
  // outputs: queue_en, queue_nxt, lvl_nxt, lvl_en
  always_comb
  begin : queue_nxt_PROC
    logic [QS+15:0] bank_mask;
    pix_t [QS+15:0] bank_shift;
    // append new data to old queue
// spyglass disable_block W486
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :Intentional '<<' and '>>', can be ignore
    bank_mask  = {{QS{1'b0}} ,{16{bank_valid&bank_accept}}} << lvl_r;
    bank_shift = {{QS{8'h00}},                   bank_data} << {lvl_r,3'b000};
    // overlay old data on bank data
    for (int b = 0; b < QS; b++)
    begin
      bank_shift[b] |= {8{~bank_mask[b]}} & queue_r[b];
    end
    bank_mask |= ~('1 << lvl_r);
    if (coef_valid & coef_accept)
    begin
      // shift by block size
      queue_en  = bank_mask >> bs;
      queue_nxt = bank_shift >> {bs,3'b000};
    end
// spyglass enable_block W486
// spyglass enable_block W164a
    else
    begin
      queue_en  = bank_mask[QS-1:0];
      queue_nxt = bank_shift[QS-1:0];
    end
    // next level
    lvl_en  = (coef_valid & coef_accept) | (bank_valid & bank_accept);
    lvl_nxt = lvl_r - 
              (coef_valid&coef_accept ? {1'b0,bs} : 6'd0) + 
              (bank_valid&bank_accept ? 6'd16: 6'd0);
    // soft reset override
    if (soft_rst)
    begin
      lvl_en  = 1'b1;
      lvl_nxt = 6'd0;
    end
  end : queue_nxt_PROC

  
  // update padding position
  // outputs: padpos_en, padpos_nxt
  always_comb
  begin : pad_PROC
    padpos_en  = 1'b0;
    padpos_nxt_a = '0;
    padpos_nxt_b = '0;
    padpos_nxt = padpos_r;
    if (in_valid & in_accept)
    begin
      // set padding position to origin
      padpos_en = 1'b1;
      padpos_nxt = unsigned'(IDX);
    end
    else if (coef_valid & coef_accept & (cf_mode == coef_mode_fm))
    begin
      // update padding position in matmat mode only
      padpos_en   = 1'b1;
      casez (coef_padlast)
      4'b111?:
        begin
        padpos_nxt_a = unsigned'(IDX);
        padpos_nxt_b = '0;
        end
      4'b110?:
        begin
        padpos_nxt_a = padpos_r;
        padpos_nxt_b = VSIZE;
        end
      4'b10??:
        begin
        padpos_nxt_a = padpos_r;
        padpos_nxt_b = 16'hfff8; //-VSIZE
        end
      4'b0???:
        begin
        padpos_nxt_a = padpos_r;
        padpos_nxt_b = VSIZE;
        end
      endcase // casez (coef_padlast)
      padpos_nxt = padpos_nxt_a + padpos_nxt_b;
    end
  end  : pad_PROC
  

  // queue registers
  // outputs: queue_r, lvl_r, padpos_r
  always_ff @(posedge clk or posedge rst_a)
  begin : queue_reg_PROC
    if (rst_a == 1'b1)
    begin
      queue_r  <= '0;
      lvl_r    <= '0;
      padpos_r <= '0;
    end
    else begin
      if (lvl_en)
      begin
        lvl_r <= lvl_nxt;
      end
      if (padpos_en)
      begin
        padpos_r <= padpos_nxt;
      end
      for (int b = 0; b < QS; b++)
      begin
        if (queue_en[b])
        begin
          queue_r[b] <= queue_nxt[b];
        end
      end
    end
  end : queue_reg_PROC


`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_ndw;
  @(posedge clk) disable iff (rst_a == 1'b1) in_valid |=> (cf_mode == coef_mode_sparse) |-> !cf_dw3;
  endproperty : prop_ndw
  p_ndw : assert property (prop_ndw) else $fatal(1, "Error: sparse mode does not support depthwise");

  property prop_n4b;
  @(posedge clk) disable iff (rst_a == 1'b1) in_valid |=> (cf_mode == coef_mode_compressed) |-> !cf_4b;
  endproperty : prop_n4b
  p_n4b : assert property (prop_n4b) else $fatal(1, "Error: compressed mode does not support 4b");
`endif
 
endmodule : npu_conv_coef_pipe

`undef SV_COUNTONES_EMULATE
