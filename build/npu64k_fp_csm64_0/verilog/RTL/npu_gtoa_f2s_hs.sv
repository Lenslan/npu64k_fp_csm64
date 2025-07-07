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
// Parameterizable block for fast to slow clock to half-clock domain handshaking
// vcs -sverilog npu_gtoa_f2s_hs.sv
//

module npu_gtoa_f2s_hs
  #(
    parameter int W = 4                                 // number of bits
  )
  (
   input  logic                    clk,                 // clock
   input  logic                    rst_a,               // reset
   input  logic                    cycle1,              // first or second cycle of half clock
   input  logic                    valid,               // input valid
   output logic                    accept,              // input accept
   input  logic [W-1:0]            data,                // input data
   output logic                    valid_mc2,           // output valid
   input  logic                    accept_mc2,          // output accept
   output logic [W-1:0]            data_mc2             // output data
   );
  // local wires
  logic                    accept_i;   // internal accept
  logic                    en;         // reg enable
  logic                    state_r;    // state
  logic                    state_nxt;  // state
  logic [W-1:0]            data_r;     // data register


  // MC paths
  npu_2cyc_checker 
    #( 
       .WIDTH          ( 1 ),
       .DISABLE_OPTION ( 1 )
       )
  u_val_mc2f2s_inst
    (
     .clk      ( clk       ),
     .rst_a    ( rst_a     ),
     .valid    ( 1'b1      ),
     .data_in  ( state_r   ),
     .data_out ( valid_mc2 )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH          ( W )
       )
  u_data_mc2f2s_inst
    (
     .clk      ( clk      ),
     .rst_a    ( rst_a    ),
     .valid    ( state_r  ),
     .data_in  ( data_r   ),
     .data_out ( data_mc2 )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH          ( 1 ),
       .DISABLE_OPTION ( 1 )
       )
  u_data_mc2s2f_inst
    (
     .clk      ( clk        ),
     .rst_a    ( rst_a      ),
     .valid    ( 1'b1       ),
     .data_in  ( accept_mc2 ),
     .data_out ( accept_i   )
     );

  assign en     = valid&accept;
  assign accept = (cycle1 & (accept_i | ~state_r));
  // next state
  always_comb
  begin : nxt_PROC
    state_nxt = state_r;
    if (cycle1)
    begin
      // clear on accept
      state_nxt &= ~accept_i;
      // set on valid
      state_nxt |= valid;
    end
  end : nxt_PROC
    
  // state register
  always_ff @(posedge clk or
              posedge rst_a)
  begin : va_del_PROC
    if (rst_a == 1'b1)
    begin
      state_r <= 1'b0;
      data_r  <= '0;
    end
    else
    begin
      state_r <= state_nxt;
      if (en)
      begin
        data_r <= data;
      end
    end
  end : va_del_PROC

endmodule : npu_gtoa_f2s_hs
