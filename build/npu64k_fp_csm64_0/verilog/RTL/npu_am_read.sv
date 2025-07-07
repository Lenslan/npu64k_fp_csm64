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
// 3D AM read interface, nested loops: [grp*no][ni*qd][col*row*onn]
//

`include "npu_defines.v"
`include "npu_am_macros.svh"

module npu_am_read
  import npu_types::*;
 #(
    parameter int DEPTH=3                           // prefetch depth
  )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  am_agu_t                 in_pars,             // AM AGU parameters
   input  logic                    in_raw_en,           // enable RAW checking
   input  logic                    in_use_acc,          // if true then initialize from AM else to 0
   input  logic                    in_keep_acc,         // if true then keep accumulator in AM else stream
   input  logic   [1:0]            in_has_aw,           // has am write before the new read
   `AMRMST(am_rd_,1),                                   // AM read interface
   output logic                    out_valid,           // Accumulator is valid
   input  logic                    out_accept,          // Accumulator is accepted
   output vyixacc_t                out_acc              // Read accumulator
   );
  //
  // Internal wires
  //
  // Parameter registers
  logic                    use_acc_r;         // useacc bit
  logic                    use_acc_en;
  logic                    usekeep;           // use_acc or keep_acc
  logic                    risky_r;           // if true then risk AM RAW hazard
  logic                    risky_nxt;
  logic       [8:0]        prod_r;            // number of inner iterations
  logic       [8:0]        prod_nxt;
  logic       [8:0]        pend_cnt_r;        // number of pending writes
  logic       [8:0]        pend_cnt_nxt;
  logic                    pend_cnt_en;
  // AGU outputs
  logic                    a_valid;           // output address is valid
  logic                    a_accept;          // output address is accepted
  logic                    a_init_acc;        // indicates first input channel and quadrant loop
  // input handshake for the use_acc FIFO
  logic                    ia_valid;
  logic                    ia_accept;
  logic                    ia_init_acc;
  // output handshake for the use_acc FIFO
  logic                    oa_valid;
  logic                    oa_accept;
  logic                    oa_init_acc;
  // output handshake for accumulator FIFO
  logic                    o_valid;
  logic                    o_accept;
  vyixacc_t                o_acc;
  // read-after-write hazards and back-to-back to same bank
  logic                    raw_haz;
  logic                    b2b_valid_r;
  logic                    b2b_bank_r;
  logic                    b2b_haz;

  //
  // Check input parameters for potential RAW hazard by checking ONN,W,H dimensions 4/5/6
  // pipeline needs to hold max of 10
  // 5 elements in the am_read FIFO, 1 reg in the dual read logic, one reg in the acc stage,
  // one reg in the dual output logic and two in the output FIFO
  //
  always_comb
  begin : risk_PROC
    // not a risk if spatial dimensions are 1 and ONN is 1 and not floating-point
    risky_nxt = in_raw_en;

    // not risky if any dimension is >=16
    if ( (|in_pars.iter[4][15:4]) || (|in_pars.iter[5][15:4]) || (|in_pars.iter[6][15:4]) )
    begin
      risky_nxt = 1'b0;
    end

    // not risky if one is >=8 and any other is >=2
    if ( (in_pars.iter[4][3] && (in_pars.iter[5][3:1]!=0 || in_pars.iter[6][3:1]!=0)) ||
         (in_pars.iter[5][3] && (in_pars.iter[4][3:1]!=0 || in_pars.iter[6][3:1]!=0)) ||
         (in_pars.iter[6][3] && (in_pars.iter[4][3:1]!=0 || in_pars.iter[5][3:1]!=0)) )
    begin
      risky_nxt = 1'b0;
    end

    // not risky if the product of the dim is >= 11
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :Ignore MSB trunk
    prod_nxt = {5'h0,in_pars.iter[4][3:0]} * {5'h0,in_pars.iter[5][3:0]} * {5'h0,in_pars.iter[6][3:0]};
// spyglass enable_block W164a
    if (prod_nxt >= 'd11)
    begin
      risky_nxt = 1'b0;
    end

  end : risk_PROC


  //
  // Parameter register
  //
  assign use_acc_en = in_valid & in_accept;
  always_ff @(posedge clk or posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1)
    begin
      use_acc_r <= 1'b0;
      risky_r   <= 1'b0;
      prod_r    <= '0;
    end
    else if (use_acc_en)
    begin
      use_acc_r <= in_use_acc;
      risky_r   <= risky_nxt;
      prod_r    <= prod_nxt;
    end
  end : reg_PROC


  //
  // Instantiate AM AGU
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally left unnconnected
  assign usekeep = in_use_acc | in_keep_acc;
  npu_am_agu
  u_agu_inst
  (
   .clk          ( clk               ),
   .rst_a        ( rst_a             ),
   .in_valid     ( in_valid          ),
   .in_accept    ( in_accept         ),
   .in_pars      ( in_pars           ),
   .in_usekeep   ( usekeep           ),
   .out_valid    ( a_valid           ),
   .out_accept   ( a_accept          ),
   .out_addr     ( am_rd_cmd_addr[0] ),
   .out_init_acc ( a_init_acc        ),
   .out_last_acc (                   ) // intentionally left unnconnected
   );
// spyglass enable_block W287b

  //
  // Drive memory read request but avoid read-after-write hazards and back-to-back accesses to same bank
  //
  always_ff @(posedge clk or posedge rst_a)
  begin : b2b_reg_PROC
    if (rst_a == 1'b1)
    begin
      b2b_valid_r <= 1'b0;
      b2b_bank_r  <= 1'b0;
    end
    else
    begin
      b2b_valid_r <= am_rd_cmd_valid[0]&am_rd_cmd_accept[0];
      b2b_bank_r  <= am_rd_cmd_addr[0][0];
    end
  end : b2b_reg_PROC
  assign b2b_haz = b2b_valid_r & (b2b_bank_r == am_rd_cmd_addr[0][0]);
`define CHK_AM_HAZ
`ifdef CHK_AM_HAZ
  assign raw_haz            = risky_r & (pend_cnt_r >= prod_r);
`else
  assign raw_haz            = 1'b0;
`endif
  assign ia_init_acc        = a_init_acc & ~use_acc_r;
  assign am_rd_cmd_valid[0] = a_valid & ia_accept & (~ia_init_acc) & (~(b2b_haz | raw_haz));
  assign a_accept           = a_valid & ia_accept & (ia_init_acc | am_rd_cmd_accept[0]) & (~(b2b_haz | raw_haz));
  assign ia_valid           = a_valid & (ia_init_acc | am_rd_cmd_accept[0]) & (~(b2b_haz | raw_haz));


  //
  // Count pending operations to detect raw hazard
  //
  always_comb
  begin : pend_PROC
    // defaults
    pend_cnt_nxt = pend_cnt_r;
    pend_cnt_en  = 1'b0;
    if (a_valid & a_accept)
    begin
      pend_cnt_en  = 1'b1;
      pend_cnt_nxt = pend_cnt_nxt + 'd1;
    end
    if (|in_has_aw)
    begin
      pend_cnt_en  = 1'b1;
    end
    pend_cnt_nxt = pend_cnt_nxt - {&in_has_aw,^in_has_aw};
  end : pend_PROC
  
  
  // pending counter register
  always_ff @(posedge clk or posedge rst_a)
  begin : pend_reg_PROC
    if (rst_a == 1'b1)
    begin
      pend_cnt_r <= '0;
    end
    else if (pend_cnt_en)
    begin
      pend_cnt_r <= pend_cnt_nxt;
    end
  end : pend_reg_PROC


  //
  // FIFO storing use_acc info
  //
  npu_fifo
  #(.SIZE   ( DEPTH ),
    .DWIDTH ( 1     ),
    .FRCVAL ( 1'b0  ),
    .FRCACC ( 1'b0  )
    )
  u_ififo_inst
    (
     .clk          ( clk          ),
     .rst_a        ( rst_a        ),
     .valid_write  ( ia_valid     ),
     .accept_write ( ia_accept    ),
     .data_write   ( ia_init_acc  ),
     .valid_read   ( oa_valid     ),
     .accept_read  ( oa_accept    ),
     .data_read    ( oa_init_acc  )
     );


  //
  // FIFO storing AM read data
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally left unnconnected
  npu_fifo
  #(.SIZE   ( DEPTH            ),
    .DWIDTH ( $bits(vyixacc_t) ),
    .FRCVAL ( 1'b0             ),
    .FRCACC ( 1'b1             ), // FIFO can always accept, guarded by the use_acc FIFO
    .LANES  ( VSIZE            )
    )
  u_dfifo_inst
    (
     .clk          ( clk          ),
     .rst_a        ( rst_a        ),
     .valid_write  ( am_rd_rvalid ),
     .accept_write (              ), // intentionally unconnected
     .data_write   ( am_rd_rdata  ),
     .valid_read   ( o_valid      ),
     .accept_read  ( o_accept     ),
     .data_read    ( o_acc        )
     );
// spyglass enable_block W287b

  //
  // Drive outputs, select 0 accumulator if init_acc and not use_acc
  //
  assign out_valid = oa_valid & (oa_init_acc | o_valid);
  assign oa_accept = out_valid & out_accept;
  assign o_accept  = oa_valid & out_accept & ~oa_init_acc;
  assign out_acc   = oa_init_acc ? '0 : o_acc;

endmodule : npu_am_read
