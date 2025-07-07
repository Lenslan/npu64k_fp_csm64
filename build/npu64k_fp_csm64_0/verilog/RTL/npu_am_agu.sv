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
// 3D AM address generator, nested loops: [grp*no][ni*qd][col*row*onn]
//

module npu_am_agu
  import npu_types::*;
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  am_agu_t                 in_pars,             // AM AGU parameters
   input  logic                    in_usekeep,          // use_acc or keep_acc
   output logic                    out_valid,           // output address is valid
   input  logic                    out_accept,          // output address is accepted
   output am_addr_t                out_addr,            // AM address
   output logic                    out_init_acc,        // If true then initialize accumulator to 0 when reading
   output logic                    out_last_acc         // If true then final write
   );
  //
  // Internal wires
  //
  // Iterator outputs
  logic      [6:0] agu_first;
  logic      [6:0] agu_last;
  // Running address register
  am_addr_t        am_addr_r;
  am_addr_t        am_addr_nxt;
  logic            am_addr_en;
  // Keep address register
  am_addr_t        am_keep_r;
  logic            am_keep_en;
  // Leep usekeep attribute
  logic            usekeep_r;


  //
  // Simple assignments
  //
  assign out_addr     = am_addr_r;
  assign out_init_acc = agu_first[3:2] == 2'b11; // in first ni and qd iteration
  assign out_last_acc = agu_last[3:2] == 2'b11;  // in last ni and qd iteration


  // store HLAPI usekeep attribute
  always_ff @(posedge clk or posedge rst_a)
  begin : usekeep_reg_PROC
    if (rst_a == 1'b1)
    begin
      usekeep_r <= 1'b0;
    end
    else if (in_valid & in_accept)
    begin
      usekeep_r <= in_usekeep;
    end
  end : usekeep_reg_PROC

  
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  //
  // Instantiate loop iterator
  //
  npu_iterator
    #(.N ( 7 ))
  u_iterator_inst
    (
    .clk      ( clk          ),
    .rst_a    ( rst_a        ),
    .soft_rst ( 1'b0         ),
    .in_req   ( in_valid     ),
    .in_ack   ( in_accept    ),
    .in_shp   ( in_pars.iter ),
    .it_req   ( out_valid    ),
    .it_ack   ( out_accept   ),
    .it_first ( agu_first    ),
    .it_last  ( agu_last     ),
    .it_vald  (              )  // intentionally unconnected
   );
// spyglass enable_block W287b


  //
  // Generate address
  //
  // next address
  // outputs: am_addr_en, am_keep_en, am_addr_nxt
  always_comb
  begin : addr_nxt_PROC
    // default outputs
    am_addr_en  = 1'b0;
    am_addr_nxt = in_pars.addr;
    am_keep_en  = 1'b0;
    // next address
    if (!in_accept)
    begin
      // update address depending on loop
      am_addr_nxt = am_addr_r + 1'b1;
      casez (agu_last[6:2])
      5'b11111:
        begin
          // end of middle loops, input channel and quadrant loops, go to next output so rebase keep
          if (!usekeep_r)
          begin
            // initialize to 0 and stream out, only intermediate in AM
            am_addr_nxt = am_keep_r;
          end
          // else just increment
        end
      5'b11100,
      5'b11110,
      5'b11101:
        begin
          // end of inner loops, go to next quadrant or input channel, reset acc pointer to keep address
          am_addr_nxt = am_keep_r;
        end
      default: 
        begin
          // in inner loops col,row,onn, increment address as per default
          am_addr_nxt = am_addr_nxt; // dummy assign
        end
      endcase // casez (agu_last)
    end
    if (in_valid && in_accept)
    begin
      // start a new address sequence
      am_addr_en = 1'b1;
      am_keep_en = 1'b1;
    end
    else if (out_valid && out_accept)
    begin
      am_addr_en = 1'b1;
      // use input accumulator from AM or write to AM
      am_keep_en = &{usekeep_r, agu_last[6:2]};
    end
  end : addr_nxt_PROC


  // Registers
  // outputs: am_addr_r, am_keep_r
  always_ff @(posedge clk or posedge rst_a)
  begin : addr_reg_PROC
    if (rst_a == 1'b1)
    begin
      am_addr_r   <= '0;
      am_keep_r   <= '0;
    end
    else
    begin
      if (am_addr_en)
      begin
        am_addr_r <= am_addr_nxt;
      end
      if (am_keep_en)
      begin
        am_keep_r <= am_addr_nxt;
      end
    end
  end : addr_reg_PROC

endmodule : npu_am_agu
