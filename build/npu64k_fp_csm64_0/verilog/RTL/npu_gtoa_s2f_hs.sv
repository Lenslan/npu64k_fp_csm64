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

module npu_gtoa_s2f_hs
  #(
    parameter int W = 4,                                // number of bits
    parameter int V = 1                                 // state vector replication width
  )
  (
   input  logic                    clk,                 // clock
   input  logic                    rst_a,               // reset
   input  logic                    cycle1,              // first or second cycle of half clock
   input  logic                    valid_mc2,           // input valid
   output logic                    accept_mc2,          // input accept
   input  logic [W-1:0]            data_mc2,            // input data
   output logic                    valid,               // output valid
   input  logic                    accept,              // output accept
   output logic [W-1:0]            data                 // output data
   );
  // derived parameters
  localparam int BPV = W/V; // bits per V
  // state type
  typedef enum logic [1:0] { state_idle_e=2'b00, state_wait_e=2'b01, state_valid_e=2'b10 } state_t;
  // local wires
  logic                    valid_i;            // internal valid
  logic                    accept_i;           // internal accept
  logic   [W-1:0]          data_i;             // data internal
  logic                    en;                 // reg enable
  logic   [V-1:0]          sel_nomerge_r;      // state, replicated
  state_t                  state_r;            // state
  state_t                  state_nxt;          // state, next
  logic [W-1:0]            data_r;             // data register


  // MC paths
  npu_2cyc_checker 
    #( 
       .WIDTH          ( 1 ),
       .DISABLE_OPTION ( 1 )
       )
  u_val_mc2s2f_inst
    (
     .clk      ( clk       ),
     .rst_a    ( rst_a     ),
     .valid    ( 1'b1      ),
     .data_in  ( valid_mc2 ),
     .data_out ( valid_i   )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH ( W )
       )
  u_data_mc2s2f_inst
    (
     .clk      ( clk      ),
     .rst_a    ( rst_a    ),
     .valid    ( 1'b1     ),
     .data_in  ( data_mc2 ),
     .data_out ( data_i   )
     );
  npu_2cyc_checker 
    #( 
       .WIDTH          ( 1 ),
       .DISABLE_OPTION ( 1 )
       )
  u_data_mc2f2s_inst
    (
     .clk      ( clk        ),
     .rst_a    ( rst_a      ),
     .valid    ( 1'b1       ),
     .data_in  ( accept_i   ),
     .data_out ( accept_mc2 )
     );

  // select output data
  always_comb
  begin : sel_PROC
    for (int v = 0; v < V; v++)
    begin
      data[BPV*v+:BPV] = sel_nomerge_r[v] ? data_r[BPV*v+:BPV] : data_i[BPV*v+:BPV];
    end
  end : sel_PROC


  // next state
  always_comb
  begin : nxt_PROC
    // defaults
    valid     = 1'b0;
    accept_i  = 1'b0;
    state_nxt = state_r;
    en        = 1'b0;
    case (state_r)
    state_valid_e:
      begin
        // register has valid data
        valid = 1'b1;
        if (accept)
        begin
          if (cycle1)
          begin
            state_nxt = state_idle_e;
          end
          else
          begin
            state_nxt = state_wait_e;
          end
        end
      end
    state_wait_e:
      begin
        // delay cycle in cycle1
        state_nxt = state_idle_e;
      end
    default: // state_idle_e
      begin
        // accept multi-cycle
        accept_i = 1'b1;
        if (cycle1)
        begin
          valid = valid_i;
          if (valid_i & (~accept))
          begin
            en        = 1'b1;
            state_nxt = state_valid_e;
          end
          // else stay in idle
        end
      end
    endcase // case (state_r)
  end : nxt_PROC
    
  // state register
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      state_r       <= state_idle_e;
      sel_nomerge_r <= '0;
      data_r        <= '0;
    end
    else
    begin
      state_r       <= state_nxt;
      sel_nomerge_r <= {V{state_nxt[1]}};
      if (en)
      begin
        data_r <= data;
      end
    end
  end : state_reg_PROC

endmodule : npu_gtoa_s2f_hs
