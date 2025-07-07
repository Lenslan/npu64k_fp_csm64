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
 * This module enumerates the loops
 */
// compile: vcs -sverilog ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv npu_gtoa_types.sv npu_gtoa_pcu_iter.sv +incdir+../../shared/RTL

module npu_gtoa_pcu_iter
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int PROG_LEN    = 12,                                      // number of instructions in activation program
    parameter int NUM_LOOPS   = 3,                                       // number of HLAPI loops
    parameter int NUM_FU      = 7,                                       // number of functional units
    parameter int ISS_SIZE    = 32                                       // maximum number of instruction slots (even/odd pairs)
    )
  (input  logic                                        clk,              // clock
   input  logic                                        rst_a,            // async reset, active high
   // interface from HLAPI
   input  logic                                        iter_req,         // request start iterations
   output logic                                        iter_ack,         // acknowledge iteration start
   input  offset_t       [NUM_LOOPS-1:0]               iter_shp,         // shape of the iterator
   input  act_inst_t     [PROG_LEN-1:0]                iter_prog,        // iteration program
   input  logic                                        iter_lay,         // accumulator layout
   // interface to instruction sequencers
   output logic                                        seq_req,          // request to start a new sequence
   input  logic                                        seq_ack,          // acknowledge start of new sequence
   output logic          [ISS_SIZE-1:0]                seq_pred,         // per instruction predicate bits
   output act_haz_inst_t [ISS_SIZE-1:0]                seq_inst,         // activation program
   input  logic                                        idle              // asserted when datapath is idle, so next 
   );
  // local types
  typedef enum logic [0:0] { state_idle, state_run } state_t;
  // local wires
  state_t                                      fsm_state_r;   // FSM state
  state_t                                      fsm_state_nxt; // FSM next state
  logic                                        fsm_state_en;  // FSM register enable
  logic                                        lay_r;         // layout mode
  logic                                        odd_r;         // if true then in odd iteration else even
  logic                                        odd_nxt;       // next state of odd_r
  logic                                        odd_en;        // enable sequencing
  logic                                        in_req;        // start new iteration
  logic                                        it_req;        // iterator valid
  logic                                        it_ack;        // iterator accept
  logic          [NUM_LOOPS-1:0]               it_first;      // first bits
  logic          [NUM_LOOPS-1:0]               it_last;       // last bits
  logic                                        it_vald;       // first/last bits valid
  act_pred_t     [ISS_SIZE-1:0]                pred_r;        // predicate bits per instruction
  act_pred_t     [ISS_SIZE-1:0]                pred_nxt;      // predicate bits per instruction, next state
  act_haz_inst_t [ISS_SIZE-1:0]                haz_inst_r;    // hazard instructions
  act_haz_inst_t [ISS_SIZE-1:0]                haz_inst_nxt;  // hazard instructions, next state
  logic                                        haz_inst_en;   // regsiter enable

  
  // simple assignments
  assign iter_ack    = (fsm_state_r == state_idle) && idle;
  assign seq_req     = (fsm_state_r == state_run) && it_req;
  assign it_ack      = (fsm_state_r == state_run) && seq_ack;
  assign odd_en      = (seq_req & seq_ack) | (iter_req & iter_ack);
  assign odd_nxt     = (~odd_r) & (~(iter_req & iter_ack));
  assign in_req      = iter_req & iter_ack;
  assign haz_inst_en = iter_req & (fsm_state_r == state_idle) & idle;
  

  //
  // Main FSM
  //

  // next state of FSM
  // outputs: fsm_state_en, fsm_state_nxt
  always_comb
  begin : fsm_nxt_PROC
    // default outputs
    fsm_state_en  = 1'b0;
    fsm_state_nxt = state_idle; 
    // state dependent
    case (fsm_state_r)
      state_run:
        begin
          if (it_req && it_ack && (&it_last))
          begin
            // done, go back to idle
            fsm_state_en  = 1'b1;
            fsm_state_nxt = state_idle;            
          end
        end
      default: // state_idle
        begin
          if (iter_req && idle)
          begin
            // decode instructions
            fsm_state_en  = 1'b1;
            fsm_state_nxt = state_run;
          end
        end
    endcase // case (fsm_state_r)
  end :  fsm_nxt_PROC
  
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected  
  //
  // HLAPI iterator
  //
  npu_iterator
    #(.N ( NUM_LOOPS )) // number of nested loops
  iter_inst
    (
     .clk      ( clk      ), // clock
     .rst_a    ( rst_a    ), // asynchronous reset, active high
     .soft_rst ( 1'b0     ), // soft reset of address generator
     .in_req   ( in_req   ), // start new iteration
     .in_ack   (          ), // acknowledge start, intentionally unconnected
     .in_shp   ( iter_shp ), // shape of the iterator
     .it_req   ( it_req   ), // iterator valid
     .it_ack   ( it_ack   ), // iterator accept
     .it_first ( it_first ), // first bits
     .it_last  ( it_last  ), // last bits
     .it_vald  (          )  // intentionally left open
     );
// spyglass enable_block W287b

  // multiply instruction decoder
  function automatic act_dec_mpy_t mpydec(
                                          logic        una, // if true then unary else binary
                                          act_bin_op_t b,   // binary opcode
                                          act_una_op_t u    // unary opcode
                                          );
    if (una)
    begin
      // unary operation
      mpydec = act_dec_mpy_t'(u - op_mac0 + dec_mac0);
    end
    else
    begin
      // binary operation
      mpydec = act_dec_mpy_t'(b - op_mpyh + dec_mpyh);
    end
  endfunction : mpydec
  
  // ALU instruction decoder
  function automatic act_dec_alu_t aludec(
                                          logic         bi,    // if 1 then binary else unary
                                          act_bin_op_t  b,     // binary opcode
                                          act_una_op_t  u      // unary opcode
                                          );
    if (!bi)
    begin
      // unary operation
      aludec = act_dec_alu_t'(u - op_getid + dec_getid);
    end
    else
    begin
      // binary operation
      aludec = act_dec_alu_t'(b - op_add + dec_add);
    end
  endfunction : aludec

  // popin instruction decoder
  function automatic act_dec_in_t indec(
                                          logic         bi,    // if 1 then binary else unary
                                          act_bin_op_t  b,     // binary opcode
                                          act_una_op_t  u      // unary opcode
                                          );
    if (!bi)
    begin
      // unary operation
      indec = act_dec_in_t'(u - op_popin + dec_popin);
    end
    else
    begin
      // binary operation
      indec = act_dec_in_t'(b - op_fpopin + dec_fpopin);
    end
  endfunction : indec

  // pushout instruction decoder
  function automatic act_dec_out_t outdec(
                                          logic         bi,    // if 1 then binary else unary
                                          act_bin_op_t  b,     // binary opcode
                                          act_una_op_t  u      // unary opcode
                                          );
    if (!bi)
    begin
      // unary operation
      outdec = act_dec_out_t'(u - op_pushout + dec_pushout);
    end
    else
    begin
      // binary operation
      outdec = act_dec_out_t'(b - op_fpushout + dec_fpushout);
    end
  endfunction : outdec

  
  //
  // Instruction decoder
  //
  // outputs: haz_inst_nxt, pred_nxt
  always_comb
  begin : dec_PROC
    // default outputs
    haz_inst_nxt           = '0;
    pred_nxt               = {ISS_SIZE{pred_never}};
    // decode
    for (int p = 0; p < PROG_LEN; p++)
    begin
      act_inst_t           ins;
      act_haz_inst_t       haz;
      logic          [7:0] m;
      ins                  = iter_prog[p];
      haz                  = '0;
      case (ins.fu)
      fu_mul0:
        begin
          haz.inst.opc.m   = mpydec(ins.fmt[2] == ot_op, ins.src2.bo, ins.src1.uo);
        end
      fu_in0, fu_in1:
        begin
          haz.inst.opc.i   = indec(ins.fmt[2] != ot_op, ins.src2.bo, ins.src1.uo);
        end
      fu_out:
        begin
          haz.inst.opc.o   = outdec(ins.fmt[2] != ot_op, ins.src2.bo, ins.src1.uo);
        end
      default:
        begin
          haz.inst.opc.a   = aludec(ins.fmt[2] != ot_op, ins.src2.bo, ins.src1.uo);
        end
      endcase
      haz.inst.ops[0]      = ins.dst;
      haz.inst.ops[1]      = ins.src0;
      haz.inst.ops[2]      = ins.src1.op.o;
      haz.inst.fmt         = ins.fmt;
`ifndef ACT_HAS_ALU1
      if (ins.fmt[2] == ot_op && (ins.src1.uo == op_selecth || ins.src1.uo == op_selectb))
      begin
        // special unary case, copy src0 to src1 so operand can use BRW
        haz.inst.ops[2]    = ins.src0;
        haz.inst.fmt[2]    = haz.inst.fmt[1];
        haz.inst.fmt[1]    = ot_no;
      end
      haz.fu               = ins.fu == fu_alu1 ? fu_alu0 : ins.fu;
`else
      haz.fu               = ins.fu;
`endif
      case (ins.fu)
        fu_mul0,
        fu_in0,
        fu_in1:         haz.lat = 3'd1;
        default:        haz.lat = 3'd0;
      endcase
      haz.src              = 8'd0;
      for (int o = 1; o < 3; o++)
      begin
        haz.src.b         |= ins.fmt[o] == ot_w;
        haz.src.b         |= ins.fmt[o] == ot_h;
        haz.src.b         |= ins.fmt[o] == ot_b;
        m                  = 8'd1<<haz.inst.ops[o];
        case (ins.fmt[o])
          ot_v: haz.src.v |= m;
          ot_s: haz.src.s |= m;
        endcase
      end      
      haz.dst              = 8'd0;
      haz.dst.b            = ins.fu == fu_bpar;
// spyglass disable_block W486
//SMD:Width mismatch
//SJ :No overflow
      m = 'd1<<haz.inst.ops[0];
// spyglass enable_block W486
      case (ins.fmt[0])
        ot_v: haz.dst.v   |= m;
        ot_s: haz.dst.s   |= m;
      endcase // case (ins.fmt[0])
      // assign to outputs
      pred_nxt[ins.pc]     = act_pred_t'(pred_nxt[ins.pc] | ins.pred);
      if (ins.pred != pred_never)
      begin
        haz_inst_nxt[ins.pc] |= haz;
      end
    end
  end : dec_PROC


  //
  // State
  //
  // outputs: fsm_state_r, odd_r, pred_r, haz_inst_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      fsm_state_r                                  <= state_idle;
      lay_r                                        <= 1'b0;
      odd_r                                        <= 1'b0;
      pred_r                                       <= {ISS_SIZE{pred_never}};
      haz_inst_r                                   <= '0;
    end
    else
    begin
      if (fsm_state_en)
      begin
        // FSM state register
        fsm_state_r                                <= fsm_state_nxt;
      end
      if (in_req)
      begin
        // inner layout mode
        lay_r                                      <= iter_lay;
      end
      if (odd_en)
      begin
        odd_r                                      <= odd_nxt;
      end
      if (haz_inst_en)
      begin
        // instruction update        
        pred_r                                     <= pred_nxt;
        haz_inst_r                                 <= haz_inst_nxt;
      end
    end
  end : state_PROC


  //
  // Derive predication bits from first/last/odd
  //
  // outputs: seq_pred
  always_comb
  begin : pred_PROC
    for (int p = 0; p < ISS_SIZE; p++)
    begin
      case (pred_r[p])
        pred_first0:  seq_pred[p] = (it_first & 3'd7) == 3'd7;
        pred_first1:  seq_pred[p] = (it_first & 3'd6) == 3'd6;
        pred_first2:  seq_pred[p] = (it_first & 3'd4) == 3'd4;
        pred_last2:   seq_pred[p] = (it_last  & 3'd4) == 3'd4;
        pred_last1:   seq_pred[p] = (it_last  & 3'd6) == 3'd6;
        pred_last0:   seq_pred[p] = (it_last  & 3'd7) == 3'd7;
        pred_nfirst0: seq_pred[p] = (it_first & 3'd7) == 3'd6;
        pred_nfirst1: seq_pred[p] = (it_first & 3'd6) == 3'd4;
        pred_nfirst2: seq_pred[p] = (it_first & 3'd4) == 3'd0;
        pred_nlast2:  seq_pred[p] = (it_last  & 3'd4) == 3'd0;
        pred_nlast1:  seq_pred[p] = (it_last  & 3'd6) == 3'd4;
        pred_nlast0:  seq_pred[p] = (it_last  & 3'd7) == 3'd6;
        pred_even:    seq_pred[p] = !odd_r;                   
        pred_odd:     seq_pred[p] = odd_r;                    
        pred_always:  seq_pred[p] = 1'b1;
        default:      seq_pred[p] = 1'b0;
      endcase // case (pred_r[p])
    end
  end : pred_PROC
    

  //
  // Expand instructions and propagate write access hazards
  //
  // outputs: seq_inst
  always_comb
  begin : out_PROC
    seq_inst = '0;
    // qualify the hazard checking signals with the predicate value
    for (int pc = 0; pc < ISS_SIZE-2; pc++)
    begin
      seq_inst[pc].inst                     = haz_inst_r[pc].inst;
      seq_inst[pc].inst.bodd                = lay_r & odd_r;
      seq_inst[pc].fu                       = haz_inst_r[pc].fu;
      seq_inst[pc].lat                      = haz_inst_r[pc].lat;
      if (seq_pred[pc])
      begin
        seq_inst[pc].src                    = haz_inst_r[pc].src;
        if (haz_inst_r[pc].lat[0])
        begin
          // 1 cycle latency
          seq_inst[pc+'d2].dst             |= haz_inst_r[pc].dst;
        end
        else
        begin
          // 0 cycles latency
          seq_inst[pc].dst                 |= haz_inst_r[pc].dst;
        end
      end
    end
    for (int pc = ISS_SIZE-2; pc < ISS_SIZE; pc++)
    begin
      seq_inst[pc].inst                     = haz_inst_r[pc].inst;
      seq_inst[pc].inst.bodd                = lay_r & odd_r;
      seq_inst[pc].fu                       = haz_inst_r[pc].fu;
      seq_inst[pc].lat                      = haz_inst_r[pc].lat;
      if (seq_pred[pc])
      begin
        seq_inst[pc].src                    = haz_inst_r[pc].src;
        seq_inst[pc].dst                 |= haz_inst_r[pc].dst;
      end
    end
  end : out_PROC

  
`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_3;
  @(posedge rst_a) NUM_LOOPS == 3;
  endproperty : prop_3
  a_p3: assert property (prop_3) else $fatal(1, "Error: HLAPI num loops needs to be 3");
  property prop_pl;
  @(posedge rst_a) PROG_LEN <= 32;
  endproperty : prop_pl
  a_pl: assert property (prop_pl) else $fatal(1, "Error: HLAPI program length not <= 31");
  for (genvar ga = 0; ga < ISS_SIZE; ga++)
  begin : ga_GEN
    property prop_fit;
    @(posedge clk) disable iff (rst_a !== 1'b0) seq_req && seq_pred[ga] |-> (ga+haz_inst_r[ga].lat) < ISS_SIZE;
    endproperty : prop_fit
    a_c1: assert property (prop_fit) else $fatal(1, "Error: Number of predicated instructions exceeds issue size");
  end : ga_GEN
`endif
  
endmodule : npu_gtoa_pcu_iter
