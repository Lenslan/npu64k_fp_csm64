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

/*
 * This module issues instructions from the sequencers to the GTOA datapath
 * An instruction sequence consists of up to ISS_SIZE/2 instruction pairs
 */
// compile: vcs -sverilog ../../shared/RTL/npu_types.sv npu_gtoa_types.sv npu_gtoa_pcu_issue.sv +incdir+../../shared/RTL
`include "npu_defines.v"

module npu_gtoa_pcu_issue
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int ISS_SIZE = 32,                                         // size of the issue table
    parameter int NUM_FU   = 7,                                          // number of functional units
    parameter int NRD      = 12                                          // number of register file read ports
    )
  (input  logic                                        clk,              // clock
   input  logic                                        rst_a,            // async reset, active high
   // interfaces from instruction sequencers
   input  logic                                        seq_req,          // instruction issue request
   output logic                                        seq_ack,          // instruction issue acknowledge
   input  logic          [ISS_SIZE-1:0]                seq_pred,         // instruction valid
   input  act_haz_inst_t [ISS_SIZE-1:0]                seq_inst,         // instruction to be issued
   output logic                                        seq_idle,         // sequencer is idle
   // instructions to functional units
   output logic          [NUM_FU-1:0]                  fu_valid,         // valid instruction per functional unit
   output act_dec_inst_t [VSIZE-1:0][NUM_FU-1:0]       fu_inst,          // instruction per lane per functional unit
   // register file read ports
   output logic          [NRD-1:0]                     rd_ren,           // read enable
   output act_op_sel_t   [NRD-1:0]                     rd_vad,           // vector read operand select
   output logic          [NRD-1:0][ACT_SREG_NUM-1:0]   rd_sad_oh,        // scalar read operand address
   output logic          [NRD-1:0]                     rd_b_oh,          // if true then parameter read
   output logic          [NRD-1:0][ISIZE-1:0]          rd_b_hi,          // if true then read upper half parameter
   output logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_wad_oh,        // word parameter read operand address
   output logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_had_oh,        // half-word parameter read operand address
   output logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_bad_oh,        // byte parameter read operand address
   // output stall
   input  logic                                        stall             // if true then stall pipeline
   );
  localparam int FU_IDX_W = $bits(act_fu_t);
  // issue table
  logic          [ISS_SIZE/2-1:0][NUM_FU-1:0]  valid_r;          // output valid
  act_haz_inst_t [ISS_SIZE/2-1:0][NUM_FU-1:0]  issue_r;          // issue table per function unit
  act_pend_t     [ISS_SIZE/2-1:0]              src_pend_r;       // pending sources
  act_pend_t     [ISS_SIZE/2-1:0]              dst_pend_r;       // pending destinations
  logic          [ISS_SIZE/2-1:0][NUM_FU-1:0]  valid_nxt;        // output valid, next state
  act_haz_inst_t [ISS_SIZE/2-1:0][NUM_FU-1:0]  issue_nxt;        // issue table per function unit, next state
  act_pend_t     [ISS_SIZE/2-1:0]              src_pend_nxt;     // next pending sources
  act_pend_t     [ISS_SIZE/2-1:0]              dst_pend_nxt;     // next pending destinations
  logic                                        enable;           // register enable
  logic                                        ok;               // OK to add new iteration
  logic                                        val_r;            // output is valid
  logic                                        val_nxt;          // next output valid
  logic                                        fu_en;            // enable instruction and register decoding
  logic          [NUM_FU-1:0]                  fu_valid_r;       // output valid per instruction
  act_dec_inst_t [VSIZE-1:0][NUM_FU-1:0]       fu_inst_nomerge_r; // output instruction
  act_dec_inst_t [NUM_FU-1:0]                  fu_inst_nxt;      // output instruction
  logic          [NRD-1:0]                     rd_ren_r;         // read enable
  act_op_sel_t   [NRD-1:0]                     rd_vad_nomerge_r; // vector read operand select
  logic          [NRD-1:0][ACT_SREG_NUM-1:0]   rd_sad_oh_r;      // scalar read operand address
  logic          [NRD-1:0]                     rd_b_oh_r;        // if true then parameter read
  logic          [NRD-1:0][ISIZE-1:0]          rd_b_hi_nomerge_r; // if true then read upper half parameter
  logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_wad_oh_r;      // word parameter read operand address
  logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_had_oh_r;      // half-word parameter read operand address
  logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_bad_oh_r;      // byte parameter read operand address
  logic          [NRD-1:0]                     rd_ren_nxt;       // read enable
  act_op_sel_t   [NRD-1:0]                     rd_vad_nxt;       // vector read operand select
  logic          [NRD-1:0][ACT_SREG_NUM-1:0]   rd_sad_oh_nxt;    // scalar read operand address
  logic          [NRD-1:0]                     rd_b_oh_nxt;      // if true then parameter read
  logic          [NRD-1:0]                     rd_b_hi_nxt;      // if true then read upper half parameter
  logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_wad_oh_nxt;    // word parameter read operand address
  logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_had_oh_nxt;    // half-word parameter read operand address
  logic          [NRD-1:0][ACT_BREG_NUM-1:0]   rd_bad_oh_nxt;    // byte parameter read operand address

  
  //
  // simple assignments
  //
  assign fu_en     = (valid_r[0] != '0) && (!stall);
  assign fu_valid  = val_r ? fu_valid_r : '0;
  assign val_nxt   = stall ? val_r : valid_r[0] != '0;
  assign fu_inst   = fu_inst_nomerge_r;
  assign enable    = ((seq_req & ok ) | (valid_r != '0)) & (~stall);
  assign seq_ack   = seq_req & ok & (~stall);
  assign seq_idle  = (valid_r == '0) && (!val_r);
  assign rd_ren    = rd_ren_r;
  assign rd_vad    = rd_vad_nomerge_r;
  assign rd_sad_oh = rd_sad_oh_r;
  assign rd_b_oh   = rd_b_oh_r;
  assign rd_b_hi   = rd_b_hi_nomerge_r;
  assign rd_wad_oh = rd_wad_oh_r;
  assign rd_had_oh = rd_had_oh_r;
  assign rd_bad_oh = rd_bad_oh_r;

  
  // shift registers and add new iteration to table
  // outputs: *nxt
  always_comb
  begin : nxt_PROC
    logic          [ISS_SIZE/2-1:0][NUM_FU-1:0] valid_add;        // appended versions
    act_haz_inst_t [ISS_SIZE/2-1:0][NUM_FU-1:0] issue_add;
    act_pend_t     [ISS_SIZE/2-1:0]             src_pend_add;
    act_pend_t     [ISS_SIZE/2-1:0]             dst_pend_add;
    act_pend_t                                  nr;               // new pending reads
    act_pend_t                                  nw;               // new pending writes
    logic          [ISS_SIZE/2-1:0]             okv;
    logic          [ISS_SIZE/2-1:0]             hraw;
    logic          [ISS_SIZE/2-1:0]             hwar;
    logic          [ISS_SIZE/2-1:0]             hwaw;
    logic          [ISS_SIZE/2-1:0]             hfu;
    // next value of state is shifted register value
    valid_nxt[ISS_SIZE/2-1]      = '0;
    issue_nxt[ISS_SIZE/2-1]      = '0;
    src_pend_nxt[ISS_SIZE/2-1]   = '0;
    dst_pend_nxt[ISS_SIZE/2-1]   = '0;
    valid_nxt[ISS_SIZE/2-2:0]    = valid_r[ISS_SIZE/2-1:1];
    issue_nxt[ISS_SIZE/2-2:0]    = issue_r[ISS_SIZE/2-1:1];
    src_pend_nxt[ISS_SIZE/2-2:0] = src_pend_r[ISS_SIZE/2-1:1];
    dst_pend_nxt[ISS_SIZE/2-2:0] = dst_pend_r[ISS_SIZE/2-1:1];
    // add new program to tables
    valid_add    = valid_nxt;
    issue_add    = issue_nxt;
    src_pend_add = src_pend_nxt;
    dst_pend_add = dst_pend_nxt;
    // check for hazards
    nr                  = '0;
    nw                  = '0;
    for (int pc = 0; pc < ISS_SIZE/2; pc++)
    begin
      // local variables
      // ensure old writes go before new reads
      nr               |= seq_inst[2*pc+0].src | seq_inst[2*pc+1].src;
      hraw[pc]          = (dst_pend_nxt[pc] & nr) != '0;
      // ensure new writes go after or together with old reads
      hwar[pc]          = (src_pend_nxt[pc] & nw) != '0;
      // ensure new writes go after old writes
      nw               |= seq_inst[2*pc+0].dst | seq_inst[2*pc+1].dst;
      hwaw[pc]          = (dst_pend_nxt[pc] & nw) != '0;
      // next state
      src_pend_add[pc] |= seq_inst[2*pc+0].src | seq_inst[2*pc+1].src;
      dst_pend_add[pc] |= seq_inst[2*pc+0].dst | seq_inst[2*pc+1].dst;
      // ensure functional units are used only once
      hfu[pc] = 1'b0;
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore
      if (seq_pred[2*pc+0])
      begin
        // single FU instruction
        hfu[pc]                            |= valid_add[pc][seq_inst[2*pc+0].fu[FU_IDX_W-1:0]];
        valid_add[pc][seq_inst[2*pc+0].fu]  = 1'b1;
        issue_add[pc][seq_inst[2*pc+0].fu]  = seq_inst[2*pc+0];
      end
      if (seq_pred[2*pc+1])
      begin
        // single FU instruction
        hfu[pc]                            |= valid_add[pc][seq_inst[2*pc+1].fu[FU_IDX_W-1:0]];
        valid_add[pc][seq_inst[2*pc+1].fu]  = 1'b1;
        issue_add[pc][seq_inst[2*pc+1].fu]  = seq_inst[2*pc+1];
      end
// spyglass enable_block SelfDeterminedExpr-ML
      // ok bit
//      if (ok &  (hraw | hwar | hwaw | hfu))
//      begin
//        $display("not ok %d (%b&%b): %d %d %d %d", pc, nw, src_pend_nxt[pc], hraw, hwar, hwaw, hfu);
//      end
      okv[pc] = ~(hraw[pc] | hwar[pc] | hwaw[pc] | hfu[pc]);
    end
    ok = &okv;
    if (seq_req && ok)
    begin
      // new can be accepted, copy add to nxt
      valid_nxt    = valid_add;
      issue_nxt    = issue_add;
      src_pend_nxt = src_pend_add;
      dst_pend_nxt = dst_pend_add;      
    end
  end : nxt_PROC
  

  //
  // State
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      valid_r    <= '0;
      issue_r    <= '0;
      src_pend_r <= '0;
      dst_pend_r <= '0;
    end
    else if (enable)
    begin
      valid_r    <= valid_nxt;
      issue_r    <= issue_nxt;
      src_pend_r <= src_pend_nxt;
      dst_pend_r <= dst_pend_nxt;
    end
  end : state_PROC

  
  // extract instructions
  // outputs: fu_inst_nxt
  always_comb
  begin : fu_inst_PROC
    for (int f = 0; f < NUM_FU; f++)
    begin
      fu_inst_nxt[f] = issue_r[0][f].inst;
    end
    if (fu_inst_nxt[fu_alu0].opc.a == dec_trnsp)
    begin
      // disable ALU write on transpose
      fu_inst_nxt[fu_alu0].fmt[0] = ot_no;
    end
  end : fu_inst_PROC

  
  // next state
  // outputs: rd*nxt
  always_comb
  begin : fu_nxt_PROC
    // default
    rd_ren_nxt    = '0;
    rd_vad_nxt    = '0;
    rd_sad_oh_nxt = '0;
    rd_b_oh_nxt   = '0;
    rd_b_hi_nxt   = '0;
    rd_wad_oh_nxt = '0;
    rd_had_oh_nxt = '0;
    rd_bad_oh_nxt = '0;
    // in0, inputs are from BW+BB
    if (valid_r[0][fu_in0])
    begin
      rd_ren_nxt[0] = fu_inst_nxt[fu_in0].fmt[1] == ot_w;
      rd_ren_nxt[1] = fu_inst_nxt[fu_in0].fmt[2] == ot_b;
      rd_wad_oh_nxt[0][fu_inst_nxt[fu_in0].ops[1]] = rd_ren_nxt[0];
      rd_bad_oh_nxt[1][fu_inst_nxt[fu_in0].ops[2]] = rd_ren_nxt[1];
      rd_b_oh_nxt[0] = rd_ren_nxt[0];
      rd_b_oh_nxt[1] = rd_ren_nxt[1];
      rd_b_hi_nxt[0] = fu_inst_nxt[fu_in0].bodd;
      rd_b_hi_nxt[1] = fu_inst_nxt[fu_in0].bodd;
    end
    // in1, inputs are from BW+BB
    if (valid_r[0][fu_in1])
    begin
      rd_ren_nxt[2] = fu_inst_nxt[fu_in1].fmt[1] == ot_w;
      rd_ren_nxt[3] = fu_inst_nxt[fu_in1].fmt[2] == ot_b;
      rd_wad_oh_nxt[2][fu_inst_nxt[fu_in1].ops[1]] = rd_ren_nxt[2];
      rd_bad_oh_nxt[3][fu_inst_nxt[fu_in1].ops[2]] = rd_ren_nxt[3];
      rd_b_oh_nxt[2] = rd_ren_nxt[2];
      rd_b_oh_nxt[3] = rd_ren_nxt[3];
      rd_b_hi_nxt[2] = fu_inst_nxt[fu_in1].bodd;
      rd_b_hi_nxt[3] = fu_inst_nxt[fu_in1].bodd;
    end
    // out, input 0 from V, 1 from BH or BB
    if (valid_r[0][fu_out])
    begin
      rd_ren_nxt[4] = fu_inst_nxt[fu_out].fmt[1] == ot_v;
      rd_ren_nxt[5] = fu_inst_nxt[fu_out].fmt[2] == ot_h || fu_inst_nxt[fu_out].fmt[2] == ot_b;
      rd_vad_nxt[4] = vr_decode(fu_inst_nxt[fu_out].fmt[1] == ot_v, fu_inst_nxt[fu_out].ops[1].v);
      rd_had_oh_nxt[5][fu_inst_nxt[fu_out].ops[2]] = fu_inst_nxt[fu_out].fmt[2] == ot_h;
      rd_bad_oh_nxt[5][fu_inst_nxt[fu_out].ops[2]] = fu_inst_nxt[fu_out].fmt[2] == ot_b;
      rd_b_oh_nxt[5] = rd_ren_nxt[5];
      rd_b_hi_nxt[5] = fu_inst_nxt[fu_out].bodd;
    end
    // alu0, input 0 from S or V, 1 from B or V, output to V or S
    if (valid_r[0][fu_alu0])
    begin
      rd_ren_nxt[6] = fu_inst_nxt[fu_alu0].fmt[1] != ot_no;
      rd_sad_oh_nxt[6][fu_inst_nxt[fu_alu0].ops[1]] = fu_inst_nxt[fu_alu0].fmt[1] == ot_s;
      rd_vad_nxt[6] = vr_decode(fu_inst_nxt[fu_alu0].fmt[1] == ot_v, fu_inst_nxt[fu_alu0].ops[1].v);
      rd_ren_nxt[7] = fu_inst_nxt[fu_alu0].fmt[2] != ot_s && fu_inst_nxt[fu_alu0].fmt[2] != ot_no;
      rd_vad_nxt[7] = vr_decode(fu_inst_nxt[fu_alu0].fmt[2] == ot_v, fu_inst_nxt[fu_alu0].ops[2].v);
      rd_wad_oh_nxt[7][fu_inst_nxt[fu_alu0].ops[2]] = fu_inst_nxt[fu_alu0].fmt[2] == ot_w;
      rd_had_oh_nxt[7][fu_inst_nxt[fu_alu0].ops[2]] = fu_inst_nxt[fu_alu0].fmt[2] == ot_h;
      rd_bad_oh_nxt[7][fu_inst_nxt[fu_alu0].ops[2]] = fu_inst_nxt[fu_alu0].fmt[2] == ot_b;
      rd_b_oh_nxt[7] = fu_inst_nxt[fu_alu0].fmt[2] == ot_w || fu_inst_nxt[fu_alu0].fmt[2] == ot_h || fu_inst_nxt[fu_alu0].fmt[2] == ot_b;
      rd_b_hi_nxt[7] = fu_inst_nxt[fu_alu0].bodd;
    end
`ifdef ACT_HAS_ALU1
    // alu1, input 0 V or BW, output to V
    if (valid_r[0][fu_alu1])
    begin
      rd_ren_nxt[8] = fu_inst_nxt[fu_alu1].fmt[1] != ot_no;
      rd_vad_nxt[8] = vr_decode(fu_inst_nxt[fu_alu1].fmt[1] == ot_v, fu_inst_nxt[fu_alu1].ops[1].v);
      rd_wad_oh_nxt[8][fu_inst_nxt[fu_alu1].ops[1]] = fu_inst_nxt[fu_alu1].fmt[1] == ot_w;
      rd_b_oh_nxt[8] = fu_inst_nxt[fu_alu1].fmt[1] == ot_w;
      rd_b_hi_nxt[8] = fu_inst_nxt[fu_alu1].bodd;
    end
`endif  // ACT_HAS_ALU1
    // mul0, input 0 from V, 1 from BH,BW or V, output to V
    if (valid_r[0][fu_mul0])
    begin
      rd_ren_nxt[9]  = fu_inst_nxt[fu_mul0].fmt[1] == ot_v;
      rd_vad_nxt[9]  = vr_decode(fu_inst_nxt[fu_mul0].fmt[1] == ot_v, fu_inst_nxt[fu_mul0].ops[1].v);
      rd_ren_nxt[10] = fu_inst_nxt[fu_mul0].fmt[2] == ot_v || fu_inst_nxt[fu_mul0].fmt[2] == ot_h || fu_inst_nxt[fu_mul0].fmt[2] == ot_w;
      rd_vad_nxt[10] = vr_decode(fu_inst_nxt[fu_mul0].fmt[2] == ot_v, fu_inst_nxt[fu_mul0].ops[2].v);
      rd_wad_oh_nxt[10][fu_inst_nxt[fu_mul0].ops[2]] = fu_inst_nxt[fu_mul0].fmt[2] == ot_w;
      rd_had_oh_nxt[10][fu_inst_nxt[fu_mul0].ops[2]] = fu_inst_nxt[fu_mul0].fmt[2] == ot_h;
      rd_b_oh_nxt[10] = fu_inst_nxt[fu_mul0].fmt[2] == ot_h || fu_inst_nxt[fu_mul0].fmt[2] == ot_w;
      rd_b_hi_nxt[10] = fu_inst_nxt[fu_mul0].bodd;
    end
    // bpar, input 0 from S
    if (valid_r[0][fu_bpar])
    begin
      rd_ren_nxt[11] = fu_inst_nxt[fu_bpar].fmt[1] == ot_s;
      rd_sad_oh_nxt[11][fu_inst_nxt[fu_bpar].ops[1]] = fu_inst_nxt[fu_bpar].fmt[1] == ot_s;
    end
  end : fu_nxt_PROC


  // state
  // outputs: val_r, fu_valid_r, fu_inst_nomerge_r, rd_ren_r, rd_vad_nomerge_r, rd_sad_oh_r, rd_b_oh_r, rd_wad_oh_r, rd_had_oh_r, rd_bad_oh_r
  always_ff @(posedge clk or
              posedge rst_a)    
  begin : lu_reg_PROC
    if (rst_a == 1'b1)
    begin
      val_r       <= 1'b0;
      fu_valid_r  <= '0;
      fu_inst_nomerge_r <= '0;
      rd_ren_r    <= '0;
      rd_vad_nomerge_r  <= '0;
      rd_sad_oh_r <= '0;
      rd_b_oh_r   <= '0;
      rd_b_hi_nomerge_r <= '0;
      rd_wad_oh_r <= '0;
      rd_had_oh_r <= '0;
      rd_bad_oh_r <= '0;
    end
    else 
    begin
      val_r         <= val_nxt;
      if (fu_en)
      begin
        fu_valid_r  <= valid_r[0];
        fu_inst_nomerge_r <= {VSIZE{fu_inst_nxt}};
        rd_ren_r    <= rd_ren_nxt;
        rd_vad_nomerge_r <= rd_vad_nxt;
        rd_sad_oh_r <= rd_sad_oh_nxt;
        rd_b_oh_r   <= rd_b_oh_nxt;
        for (int r = 0; r < NRD; r++)
        begin
          rd_b_hi_nomerge_r[r] <= {ISIZE{rd_b_hi_nxt[r]}};
        end
        rd_wad_oh_r <= rd_wad_oh_nxt;
        rd_had_oh_r <= rd_had_oh_nxt;
        rd_bad_oh_r <= rd_bad_oh_nxt;
      end
    end
  end : lu_reg_PROC
  
  
`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_ackempty;
  @(posedge clk) disable iff (rst_a !== 1'b0) seq_req && (valid_r == '0) && (!stall) |-> seq_ack;
  endproperty : prop_ackempty
  a_ackempty: assert property (prop_ackempty) else $fatal(1, "Error: cannot issue program, exceeds issue table size?");
`endif
  

endmodule : npu_gtoa_pcu_issue
