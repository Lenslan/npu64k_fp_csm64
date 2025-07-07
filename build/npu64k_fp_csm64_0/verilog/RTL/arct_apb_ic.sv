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

`include "npu_apb_macros.svh"

module arct_apb_ic 
 #(
   parameter int CLIENTS = 16,   //  number of clients
   parameter int ADDR_OFFSET = 0 // [:17] msb of address
 )
 (
  input  logic                            clk,                    // debug apb clock
  input  logic                            rst_a,                  // debug apb asnyc reset, active low
  input  logic                            test_mode,              // disable reset sync in tst mode
  // APB_IC slave: address 32b, data 32b, prefix i_
  `APBSLV(32,32,i_),
  // APB_IC multiple master: address 16b, data 32b, prefix i_
  `APBMSTN(CLIENTS,16,32,o_)
  );
  // local wires
  logic               rst;
  logic               csel_en;
  logic [CLIENTS+1:0] csel_nxt;
  logic [CLIENTS+1:0] csel_r;
  logic [11:2]        addr_r;
  logic [31:0]        rom_prdata;
  `APBWIRES(32,32,i0_);
  `APBWIRES(32,32,i1_);
  `APBWIRESN(CLIENTS,16,32,o0_);
  `APBWIRESN(CLIENTS,16,32,o1_);

  
localparam DB_CSR1_PARM     = 32'h0000_0010;
localparam DB_CSR2_PARM     = 32'h24B0_0005;
localparam DB_CSR3_PARM     = 32'h0;
localparam DB_CSR4_PARM     = 32'h0;
localparam DB_CSR5_PARM     = 32'h0;

  // input APB slice
  arct_apb_slice
  #(.AW (32))
  u_in0_slice
  (
  .clk       ( clk       ),
  .rst_a     ( rst_a     ),
  .test_mode ( test_mode ),
  `APBINST(i_,i_),
  `APBINST(o_,i0_)
  );
  arct_apb_slice
  #(.AW (32))
  u_in1_slice
  (
  .clk       ( clk       ),
  .rst_a     ( rst_a     ),
  .test_mode ( test_mode ),
  `APBINST(i_,i0_),
  `APBINST(o_,i1_)
  );
  // output APB slices
  for (genvar gi = 0; gi < CLIENTS; gi++)
  begin : out_slice_GEN
    arct_apb_slice
    #(.AW (16))
    u_out0_slice
    (
     .clk       ( clk       ),
     .rst_a     ( rst_a     ),
     .test_mode ( test_mode ),
     `APBINSTM(gi,i_,o0_),
     `APBINSTM(gi,o_,o1_)
    );
    arct_apb_slice
    #(.AW (16))
    u_out1_slice
    (
     .clk       ( clk       ),
     .rst_a     ( rst_a     ),
     .test_mode ( test_mode ),
     `APBINSTM(gi,i_,o1_),
     `APBINSTM(gi,o_,o_)
    );
  end : out_slice_GEN
 
  
  // simple assignments
  assign o0_psel    = {CLIENTS{i1_psel}} & csel_nxt[1+:CLIENTS];
  assign o0_penable = {CLIENTS{i1_penable}} & csel_r[1+:CLIENTS];
  assign o0_paddr   = {CLIENTS{4'b0,i1_paddr[11:2]}};
  assign o0_pwrite  = {CLIENTS{i1_pwrite}};
  assign o0_pwdata  = {CLIENTS{i1_pwdata}};
// spyglass disable_block Ac_conv01
// SMD: 37 synchronizers converge on combinational gate 'npu_core_aon.u_npu_top_aon.u_dw_apbic_inst.i1_pready
// SJ: Reset will not turn with invert direction at same time.
  assign i1_pready  = |{(o0_pready & csel_r[1+:CLIENTS]), csel_r[0], csel_r[CLIENTS+1]};
// spyglass enable_block Ac_conv01
  assign csel_en   = i1_psel & (~i1_penable);


  // instance reset synchronizer
  npu_reset_ctrl 
  u_sync_rst
  (
    .clk        ( clk       ),
    .rst_a      ( rst_a     ),
    .test_mode  ( test_mode ),
    .rst        ( rst       )
  );


// spyglass disable_block Reset_check07
// SMD: Reset is dirven by comb logic
// SJ: Reset control module is not recongnized correctly
  // store selected slave
  always_ff @(posedge clk or posedge rst)
  begin : reg_PROC
    if (rst == 1'b1)
    begin
      csel_r <= '0;
      addr_r <= '0;
    end
    else if (csel_en)
    begin
      csel_r <= csel_nxt;
      addr_r <= i1_paddr[11:2];
    end
  end : reg_PROC
// spyglass enable_block Reset_check07

  
  // addresss decoder
  //   bits 31:17 are APB base address
  //   bits [16:12]==0 is ROM table
  //   bits [16:12]!=0 is client
  //   bits [16:12]>client --> return error
  always_comb
  begin : dec_PROC
    csel_nxt = '0;
    if (i1_psel)
    begin
      if (i1_paddr[31:17] == ADDR_OFFSET)
      begin
        for (int i = 0; i <= CLIENTS; i++)
        begin
// spyglass disable_block W362
// SMD: LHS is 5bits while RHS is 32bits
// SJ: Loop VAR from 0 to CLIENTS, no exceed
          csel_nxt[i] = i1_paddr[16:12] == unsigned'(i);
// spyglass enable_block W362
        end
      end
      // rom cannot write
      csel_nxt[0] &= ~i1_pwrite;
      // default slave returns error
      csel_nxt[CLIENTS+1] = csel_nxt[CLIENTS:0] == '0;
    end
  end : dec_PROC


  // response selection
  // outputs: i1_prdata, i1_pslverr
  always_comb
  begin : resp_PROC
    // default outputs
    i1_prdata  = '0;
    i1_pslverr = '0;
    // read ROM table (no error)
    i1_prdata    |= rom_prdata & {32{csel_r[0]}};
    // read clients
    for (int c = 0; c < CLIENTS; c++)
    begin
      i1_prdata  |= o0_prdata[c] & {32{csel_r[c+1]}};
      i1_pslverr |= o0_pslverr[c] & csel_r[c+1];
    end
    // default slave always returns error
    i1_pslverr   |= csel_r[CLIENTS+1];
  end: resp_PROC


  // rom table read
  // outputs: rom_prdata
  always_comb
  begin : rom_PROC
    case ({addr_r,2'b00})
    12'h400: rom_prdata = DB_CSR1_PARM;  // DB_CSR1
    12'h404: rom_prdata = DB_CSR2_PARM;  // DB_CSR2
    12'h408: rom_prdata = DB_CSR3_PARM;  // DB_CSR3
    12'h40c: rom_prdata = DB_CSR4_PARM;  // DB_CSR4
    12'h410: rom_prdata = DB_CSR5_PARM;  // DB_CSR5
    12'hFCC: rom_prdata = 32'b0;         // memory_type
    12'hFD0: rom_prdata = {24'h0,8'h04}; // PIDR4 // [7:4] size // [3:0] DES_2
    12'hFD4: rom_prdata = {24'h0,8'h00}; // PIDR5 // reserv
    12'hFD8: rom_prdata = {24'h0,8'h00}; // PIDR6 // reserv
    12'hFDC: rom_prdata = {24'h0,8'h00}; // PIDR7 // reserv
    12'hFE0: rom_prdata = {24'h0,8'h01}; // PIDR0 // [7:0] Part number bits
    12'hFE4: rom_prdata = {24'h0,8'h80}; // PIDR1 // [7:4] JEP106 identification code bits[3:0] // [3:0] Part number bits[11:8]
    12'hFE8: rom_prdata = {24'h0,8'h0D}; // PIDR2 // [7:4] Revision // [3] JEDEC // [2:0] JEP106 identification code[6:4]
    12'hFEC: rom_prdata = {24'h0,8'h00}; // PIDR3 // [7:4] RevAnd // [3:0] Customer Modified
    12'hFF0: rom_prdata = {24'h0,8'h0D}; // CIDR0 // [7:0] Preamble 0 (0x0D)
    12'hFF4: rom_prdata = {24'h0,8'h10}; // CIDR1 // [7:4] Component class (0x1 – Class 0x1 Rom Table) [3:0] Preamble 1 (0x0)
    12'hFF8: rom_prdata = {24'h0,8'h05}; // CIDR2 // [7:0] Preamble 2 (0x05)
    12'hFFC: rom_prdata = {24'h0,8'hB1}; // CIDR3 // [7:0] Preamble 3 (0xB1)
    default:
      begin
        if (addr_r < unsigned'(CLIENTS))
        begin
          logic [5:0] client;
          client = addr_r[7:2] + 1'b1;
          rom_prdata = {14'h0,client, // [31:12] entry offset
                        3'b0, // [11:9] reserv
                        5'd0, // [8:4] pwrid
                        1'b0, // [3] reserv
                        1'b0, // [2] pwrvld
                        1'b1, // [1] 32-bit format
                        1'b1  // [0] present 
                        };
        end
        else
        begin
          rom_prdata = '0;
        end
      end
    endcase // case ({addr_r,2'b00})
  end : rom_PROC
  
endmodule : arct_apb_ic
