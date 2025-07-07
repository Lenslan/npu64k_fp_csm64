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
 * This module implements the ALU functional unit
 * All operations execute in 1 cycle
 */
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv npu_gtoa_types.sv npu_gtoa_fu_alu.sv npu_gtoa_fu_alu_lut.sv -y $SYNOPSYS/dw/sim_ver +libext+.v
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../npu_gtoa_types.sv ../npu_gtoa_fu_alu.sv ../npu_gtoa_fu_alu_lut.sv"

module npu_gtoa_fu_alu
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int ID  = 1,                                           // ALU instance ID: 0 has reduce and LUT, 1 simple
    parameter int VID = 0                                            // vector lane ID
    )
  (
   input  logic                                       clk,           // clock
   input  logic                                       rst_a,         // asynchronous reset, active high
   // strap input
   input  logic             [7:0]                     slc_id,        // unique slice ID
   // instruction
   input  logic                                       fu_valid,      // instruction valid per functional unit
// spyglass disable_block W240
//SMD:Unread input
//SJ :Macro defined packed signal can be ignore
   input  act_dec_inst_t                              fu_inst,       // instruction to be executed per functional units
// spyglass enable_block W240
   // three register read interfaces
   input  ixacc_t           [1:0]                     rd_data,       // read data
   // one register write interface
   output act_ot_t                                    wr_typ,        // write operand type
   output logic             [2:0]                     wr_ad,         // write operand address
   output ixacc_t                                     wr_data,       // write data
   // transpose
   output logic                                       rf_trnsp,      // transpose instruction
   // input alu state
   input  logic                                       in_state_en,   // input ALU state enable
   input  logic             [ISIZE-1:0]               in_state,      // input ALU state
   // reduction input, incoming rd_data from another lane!
   input  ixacc_t           [1:0]                     red_inp,
   output logic             [ISIZE-1:0]               red_state_out,
   input  logic             [ISIZE-1:0]               red_state_in,
   input  acc_t                                       rd_vr7i0,      // read data from vr7 i0
`ifndef ACT_HAS_ALU1
   // spatial shift and broadcast interface
   input  ixacc_t                                     shv_in,        // shv input
   input  ixacc_t                                     bcv_in,        // spatial broadcast input
`endif
`ifdef ACT_HAS_ALU1
   output logic             [ISIZE-1:0]               alu_state,     // ALU state to ALU1
`else  // ACT_HAS_ALU1
   // LUT table
   input  act_lutt_t                                  lut_data,
   // queue  interface, no back-pressure, compile should have scheduled correctly
   output logic             [1:0]                     q_in_valid,    // lut queue valid
   output ix_fplut_queue_t  [1:0]                     q_in_data,     // lut queue data
`endif  // ACT_HAS_ALU1
   // flow control
   input  logic                                       stall          // stall
   );
  // local wires
  logic                               state_dec;     // ALU state instruction decoded
  logic                               state_en;      // ALU state enable
  logic        [ISIZE-1:0]            state_r;       // ALU state
  logic        [ISIZE-1:0]            state_nxt;     // ALU state next
`ifndef ACT_HAS_ALU1
  logic                               lut_wq;        // look-up table queue write data
  ixacc_t                             lut_res;       // look-up table result
`endif  // ACT_HAS_ALU1
  fp_oh_idx_t                         falu_opc_oh;   // one-hot floating-point ALU
  ixacc_t                             falu_a;        // fp ALU input a
  ixacc_t                             falu_b;        // fp ALU input b
  ixacc_t                             falu_res;      // fp ALU result
  ixacc_t                             redc_a;        // channel reduce input a
  ixacc_t                             redc_b;        // channel reduce input b
  ixacc_t                             add_a;         // adder input a
  ixacc_t                             add_b;         // adder input b
  logic        [ISIZE-1:0]            add_cin;       // adder carry in
  ixacc_t                             add_sum;       // adder sum
  logic        [ISIZE-1:0]            add_neg;       // adder overflow
  logic        [ISIZE-1:0]            eq;            // equal comparison
  logic        [ISIZE-1:0][63:0]      shift_in;      // shifter input
  logic        [ISIZE-1:0][5:0]       shamt;         // shift amount
  logic        [ISIZE-1:0][63:0]      shift_out;     // shifter output
  
  
  // simple assignments
  assign wr_typ     = fu_valid ? fu_inst.fmt[0] : ot_no;
  assign wr_ad      = fu_inst.ops[0];
  assign rf_trnsp   = fu_valid & (fu_inst.opc.a == dec_trnsp);
`ifdef ACT_HAS_ALU1
  assign alu_state  = state_r;
`else  // ACT_HAS_ALU1
  assign q_in_valid = (fu_valid & ~stall) ? {2{lut_wq}} : 2'b00;  
`endif  // ACT_HAS_ALU1

  
  function automatic logic [63:0] sext64(acc_t a);
    sext64 = {{32{a[31]}}, a};
  endfunction: sext64

  function automatic logic [63:0] zext64(acc_t a);
    zext64 = {32'h0, a[31:0]};
  endfunction: zext64


`ifndef ACT_HAS_ALU1
  //
  // LUT instructions
  //
  npu_gtoa_fu_alu_lut
  u_lut_inst
  (
   .clk           ( clk           ),
   .rst_a         ( rst_a         ),
   .valid         ( fu_valid      ),
   .stall         ( stall         ),
   .lut_data      ( lut_data      ),
   .opc           ( fu_inst.opc.a ),
   .rd_data       ( rd_data[0]    ),
   .res           ( lut_res       ),
   .q_data        ( q_in_data     )
  );
`endif

  
  //
  // Channel reducation inputs
  //
  always_comb
  begin : red_in_PROC
    // channel reduction inputs
    redc_a = '0;
    redc_b = '0;
    for (int i = 0; i < ISIZE/2; i++)
    begin
      redc_a[i]   = rd_data[0][2*i+0];
      redc_b[i]   = rd_data[0][2*i+1];
    end
  end : red_in_PROC
  

  //
  // FP ALU opcode
  //
  // outputs: falu_opc_oh
  always_comb
  begin : alu_opc_PROC
    falu_opc_oh = '0;
    case (fu_inst.opc.a)
    dec_ftoi:   falu_opc_oh[fp_ftoi_oh_idx]   = 1'b1;
    dec_itof:   falu_opc_oh[fp_itof_oh_idx]   = 1'b1;
    dec_trunc:  falu_opc_oh[fp_trunc_oh_idx]  = 1'b1;
    dec_fract:  falu_opc_oh[fp_fract_oh_idx]  = 1'b1;
    dec_renorm: falu_opc_oh[fp_renorm_oh_idx] = 1'b1;
    default:    falu_opc_oh[fp_add_oh_idx]    = 1'b1;
    endcase // case (fu_inst.opc.a)
  end : alu_opc_PROC

  
  //
  // ALU datapath inputs
  //
  // outputs: shift_in, shamt, add_a, add_b, add_cin, falu_a, falu_b
  always_comb
  begin : alu_dp_in_PROC

    // shifter input logic
    shift_in = '0;
    shamt    = '0;
    case (fu_inst.opc.a)
    dec_asr:
      begin
        // signed shift right, result is in position [31+:32]
        for (int i = 0; i < ISIZE; i++)
        begin
          shift_in[i] |= sext64(rd_data[0][i]);
          shamt[i]    |= {rd_data[1][i][5], ~rd_data[1][i][4:0]};
        end
      end
    dec_lsr:
      begin
        // unsigned shift right, result is in position [31+:32]
        for (int i = 0; i < ISIZE; i++)
        begin
          shift_in[i] |= zext64(rd_data[0][i]);
          shamt[i]    |= {rd_data[1][i][5], ~rd_data[1][i][4:0]};
        end
      end
    default: // dec_sl:
      begin
        // signed shift left, result is in position [32+:32]
        for (int i = 0; i < ISIZE; i++)
        begin
          shift_in[i] |= sext64(rd_data[0][i]);
          shamt[i]    |= {~rd_data[1][i][5], rd_data[1][i][4:0]};
        end
      end
    endcase // case (fu_inst.opc.a)

    // Data path integer adder inputs
    add_a   = '0;
    add_b   = '0;
    add_cin = '0;
    case (fu_inst.opc.a) 
    dec_lt, dec_lte, dec_relun, dec_min, dec_sub:
      begin
        // subtract A-B, sign bit of output used in comparison
        add_a   |= rd_data[0];
        add_b   |= ~rd_data[1];
        add_cin |= '1;
      end
    dec_flt, dec_flte, dec_frelun, dec_frelunf, dec_fmin, dec_fminf:
      begin
        // subtract A-B, invert non-sign bits if negative
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {1'b0, {31{rd_data[0][i][31]}}} ^ rd_data[0][i];
          add_b[i]   |= {1'b1, {31{~rd_data[1][i][31]}}} ^ rd_data[1][i];
          add_cin[i] |= 1'b1;
        end
      end
    dec_rminc:
      begin
        // subtract A-B, invert non-sign bits if negative
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {1'b0, {31{redc_a[i][31]}}} ^ redc_a[i];
          add_b[i]   |= {1'b1, {31{~redc_b[i][31]}}} ^ redc_b[i];
          add_cin[i] |= 1'b1;
        end
      end
    dec_rminv:
      begin
        // subtract A-B, invert non-sign bits if negative
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {1'b0, {31{red_inp[0][i][31]}}} ^ red_inp[0][i];
          add_b[i]   |= {1'b1, {31{~red_inp[1][i][31]}}} ^ red_inp[1][i];
          add_cin[i] |= 1'b1;
        end
      end
    dec_gt, dec_gte, dec_max, dec_rsub:
      begin
        // subtract B-A, sign bit of output used in comparison
        add_a   |= ~rd_data[0];
        add_b   |= rd_data[1];
        add_cin |= '1;
      end
`ifndef ACT_HAS_ALU1
    dec_frelu,
`endif
    dec_fgt, dec_fgte, dec_fmax, dec_fmaxf:
      begin
        // subtract B-A, invert non-sign bits if negative
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {1'b1, {31{~rd_data[0][i][31]}}} ^ rd_data[0][i];
          add_b[i]   |= {1'b0, {31{rd_data[1][i][31]}}} ^ rd_data[1][i];
          add_cin[i] |= 1'b1;
        end
      end
    dec_rmaxc:
      begin
        // subtract B-A, invert non-sign bits if negative
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {1'b1, {31{~redc_a[i][31]}}} ^ redc_a[i];
          add_b[i]   |= {1'b0, {31{redc_b[i][31]}}} ^ redc_b[i];
          add_cin[i] |= 1'b1;
        end
      end
    dec_rmaxv:
      begin
        // subtract B-A, invert non-sign bits if negative
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {1'b1, {31{~red_inp[0][i][31]}}} ^ red_inp[0][i];
          add_b[i]   |= {1'b0, {31{red_inp[1][i][31]}}} ^ red_inp[1][i];
          add_cin[i] |= 1'b1;
        end
      end
    dec_abs:
      begin
        // absolute value, negate if negative input
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i]   |= {32{rd_data[0][i][31]}} ^ rd_data[0][i];
          add_cin[i] |= rd_data[0][i][31];
        end
      end
`ifndef ACT_HAS_ALU1
    dec_selecth:
      begin
        // add fixed offset respectively on high/low exponents
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i] |= {1'd0, 3'd0, rd_data[1][i][30:26], 5'd0, 3'd0, rd_data[1][i][14:10], 10'd0};
          add_b[i] |= {1'd0,                     8'd112, 5'd0,                     8'd112, 10'd0};
        end
      end
`endif  // ACT_HAS_ALU1
    dec_eadd:
      begin
        // add a's exponent with b
        for (int i = 0; i < ISIZE; i++)
        begin
          add_a[i] |= {24'h0, rd_data[0][i][30:23]};
          add_b[i] |= {{23{rd_data[1][i][8]}}, rd_data[1][i][8:0]};
        end
      end
    default: // dec_add:
      begin
        // add A with B
        add_a   |= rd_data[0];
        add_b   |= rd_data[1];
      end
    endcase // case (fu_inst.opc.a)
    
    // Data path floating-point adder inputs
    falu_a = '0;
    falu_b = '0;
    case (fu_inst.opc.a) 
    dec_mirror:
      begin
        // channel 0 : 2*B - A
        // the 2*B part is read from pre-computed result in vr7 i0
        falu_a[0]   |= {~rd_data[0][0][31], rd_data[0][0][30:0]};
        falu_b[0]   |= rd_vr7i0;
        // channel 1 : B - A
        falu_a[1]   |= {~rd_data[0][0][31], rd_data[0][0][30:0]};
        falu_b[1]   |= rd_data[1][0];
      end
    dec_replic:
      begin
        // channel 0 : 2*B - 1.0 - A
        // the (2*B - 1.0) part is read from pre-computed result in vr7 i0
        falu_a[0]   |= {~rd_data[0][0][31], rd_data[0][0][30:0]};
        falu_b[0]   |= rd_vr7i0;
        // channel 1 : B - A
        falu_a[1]   |= {~rd_data[0][0][31], rd_data[0][0][30:0]};
        falu_b[1]   |= rd_data[1][0];
        // channel 2 : -1.0 - A
        falu_a[2]   |= {~rd_data[0][0][31], rd_data[0][0][30:0]};
        falu_b[2]   |= 32'hbf800000;
      end
    dec_fsub, dec_fsubf:
      begin
        // subtract A-B, sign bit of output used in comparison
        falu_a      |= rd_data[0];
        for (int i = 0; i < ISIZE; i++)
        begin
          falu_b[i] |= {~rd_data[1][i][31], rd_data[1][i][30:0]};
        end
      end
    dec_frsub, dec_frsubf:
      begin
        // subtract B-A, sign bit of output used in comparison
        for (int i = 0; i < ISIZE; i++)
        begin
          falu_a[i] |= {~rd_data[0][i][31], rd_data[0][i][30:0]};
        end
        falu_b      |= rd_data[1];
      end
    dec_raddv:
      begin
        falu_a      |= red_inp[0];
        falu_b      |= red_inp[1];
      end
    dec_raddc:
      begin
        falu_a      |= redc_a;
        falu_b      |= redc_b;
      end
    default : // dec_fadd, dec_itof, dec_ftoi, dec_fract, dec_trunc, dec_renorm
      begin
        falu_a      |= rd_data[0];
        falu_b      |= rd_data[1];
      end
    endcase // case (fu_inst.opc.a)
  end : alu_dp_in_PROC
  

  //
  // Datapath functions
  //
  for (genvar gi = 0; gi < ISIZE; gi++)
  begin : dp_GEN
    // floating-point ALU
    npu_gtoa_fu_alu_fp
    u_falu_inst
    (
     .opc_oh ( falu_opc_oh  ),
     .a      ( falu_a[gi]   ),
     .b      ( falu_b[gi]   ),
     .z      ( falu_res[gi] )
    );
    // integer adder
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    assign {add_neg[gi],add_sum[gi]} = {add_a[gi][31],add_a[gi]} + {add_b[gi][31],add_b[gi]} + {32'h0,add_cin[gi]};
// spyglass enable_block W164a
    // integer shifter
    assign shift_out[gi] = shift_in[gi] << shamt[gi];
  end : dp_GEN

  
  //
  // ALU output selection
  //
  // outputs: wr_data, state_dec, lut_wq
  always_comb
  begin : alu_dp_out_PROC
    logic [ISIZE-1:0]  state_i;       // ALU state internal
    logic [ISIZE-1:0]  a_zero;        // input a is zero
    logic [ISIZE-1:0]  b_zero;        // input b is zero
    logic [ISIZE-1:0]  a_nan;         // input a is nan
    logic [ISIZE-1:0]  b_nan;         // input b is nan
    logic [ISIZE-1:0]  feq;           // floating equal flag
    ixacc_t     [1:0]  sel_in;        // select data for min/max

    // set zero and nan for floating comparison
    sel_in = '0;
    for (int i = 0; i < ISIZE; i++)
    begin
      case (fu_inst.opc.a)
      dec_rmaxv, dec_rminv:
        begin
          sel_in[0][i] |= red_inp[0][i];
          sel_in[1][i] |= red_inp[1][i];
        end
      dec_rmaxc, dec_rminc:
        begin
          sel_in[0][i] |= redc_a[i];
          sel_in[1][i] |= redc_b[i];
        end
      default:
        begin
          sel_in[0][i] |= rd_data[0][i];
          sel_in[1][i] |= rd_data[1][i];
        end
      endcase // case (fu_inst.opc.a)
      a_zero[i] = ~(|sel_in[0][i][30:23]);
      b_zero[i] = ~(|sel_in[1][i][30:23]);
      a_nan[i]  = &sel_in[0][i][30:23];
      b_nan[i]  = &sel_in[1][i][30:23];
      eq[i]     = sel_in[0][i] == sel_in[1][i];
      // set subnormal inputs to zero
      sel_in[0][i][22:0] &= {23{~a_zero[i]}};
      sel_in[1][i][22:0] &= {23{~b_zero[i]}};
      // floating equal: equal and neither nan, or both zero
      feq[i] = (eq[i] & ~a_nan[i] & ~b_nan[i]) | (a_zero[i] & b_zero[i]);
    end

    // default outputs
    state_dec = 1'b0;
`ifndef ACT_HAS_ALU1
    lut_wq    = 1'b0;
`endif
    
    // select result
    wr_data = '0;
    state_i = '0;
    red_state_out = '0;
    case (fu_inst.opc.a) 
    dec_gt, dec_lt:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= rd_data[0][i];
          state_i[i]  = add_neg[i];
        end
        state_dec = 1'b1;
      end
    dec_gte, dec_lte:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= rd_data[0][i];
          state_i[i]  = add_neg[i] | eq[i];
        end     
        state_dec = 1'b1;
      end
    dec_eq:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= rd_data[0][i];
          state_i[i]  = eq[i];
        end
        state_dec = 1'b1;
      end
    dec_neq:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= rd_data[0][i];
          state_i[i]  = ~eq[i];
        end
        state_dec = 1'b1;
      end
    dec_fadd, 
    dec_fsub,
    dec_frsub,
    dec_raddv, 
    dec_raddc,
    dec_ftoi,
    dec_itof,
    dec_renorm,
    dec_fract,
    dec_trunc:
      begin
        wr_data |= falu_res;
      end
    dec_max, dec_min:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= add_neg[i] ? rd_data[0][i] : rd_data[1][i];
        end
      end
    dec_select:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= state_r[i] ? rd_data[0][i] : rd_data[1][i];
        end     
      end
`ifndef ACT_HAS_ALU1
    dec_selecth:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          if (state_r[i])
          begin
            // select high
            wr_data[i][31] |= rd_data[1][i][31];
            case (rd_data[1][i][30:26])
            5'h00:
              begin
                // zero
                wr_data[i][30:23] |= 8'h00;
              end
            5'h1f:
              begin
                // fp16 exp is 0x1f, set 0xff for fp32 exp
                wr_data[i][30:13] |= {8'hff, rd_data[1][i][25:16]};
              end
            default:
              begin
                // exp += 112
                wr_data[i][30:13] |= {add_sum[i][30:23], rd_data[1][i][25:16]};
              end
            endcase // case (rd_data[1][i][30:26])            
          end
          else
          begin
            // select low
            wr_data[i][31] |= rd_data[1][i][15];
            case (rd_data[1][i][14:10])
            5'h00:
              begin
                // zero
                wr_data[i][30:23] |= 8'h00;
              end
            5'h1f:
              begin
                // fp16 exp is 0x1f, set 0xff for fp32 exp
                wr_data[i][30:13] |= {8'hff, rd_data[1][i][9:0]};
              end
            default:
              begin
                // exp += 112
                wr_data[i][30:13] |= {add_sum[i][17:10], rd_data[1][i][9:0]};
              end
            endcase // case (rd_data[1][i][14:10])
          end
        end
      end // case: dec_selecth
    dec_selectb:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= state_r[i] ? {rd_data[1][i][31:16], 16'h0} : {rd_data[1][i][15:0], 16'h0};
        end
      end
`endif  // ACT_HAS_ALU1
    dec_relun:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          if (add_neg[i])
            wr_data[i] |= rd_data[0][i][31] ? '0 : rd_data[0][i];
          else
            wr_data[i] |= rd_data[1][i][31] ? '0 : rd_data[1][i];
        end     
      end
    dec_band:
      begin
        wr_data |= rd_data[0] & rd_data[1];
      end
    dec_bor:
      begin
        wr_data |= rd_data[0] | rd_data[1];
      end
    dec_bnot:
      begin
        wr_data |= ~rd_data[0];
      end
    dec_bxor:
      begin
        wr_data |= rd_data[0] ^ rd_data[1];
      end
    dec_rorv:
      begin
        wr_data |= red_inp[0] | red_inp[1];
      end
    dec_randv:
      begin
        wr_data |= red_inp[0] & red_inp[1];
      end
    dec_rorc:
      begin
        wr_data |= redc_a | redc_b;
      end
    dec_randc:
      begin
        wr_data |= redc_a & redc_b;
      end
`ifndef ACT_HAS_ALU1
    dec_bcv:
      begin
        wr_data |= bcv_in;
      end
    dec_bcc:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= rd_data[0][0];
        end
      end
`endif
    dec_sat8:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i][6:0]  |= {24{rd_data[0][i][31]}} == rd_data[0][i][30:7] ? rd_data[0][i][6:0] : {7{~rd_data[0][i][31]}};
          wr_data[i][31:7] |= {25{rd_data[0][i][31]}};
        end
      end
    dec_sat16:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i][14:0]  |= {16{rd_data[0][i][31]}} == rd_data[0][i][30:15] ? rd_data[0][i][14:0] : {15{~rd_data[0][i][31]}};
          wr_data[i][31:15] |= {17{rd_data[0][i][31]}};
        end
      end
    dec_eadd:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i][31] |= rd_data[0][i][31];
          if (!add_neg[i])
          begin
            if ((add_sum[i][9:8] != 2'b00) || (add_sum[i][7:0] == 8'hff))
              // exp overflow or equal to 255, return +/- nan
              wr_data[i][30:0] |= 31'h7fffffff;
            else
              // use sum of exp
              wr_data[i][30:0] |= {add_sum[i][7:0], sel_in[0][i][22:0]};
          end
          // else 0
        end
      end
    dec_mirror:
      begin
        if (a_nan[0])
        begin
          wr_data[0] |= sel_in[0][0];
        end
        else if (b_nan[0])
        begin
          wr_data[0] |= (sel_in[0][0][31] & ~a_zero[0]) ? {~sel_in[0][0][31], sel_in[0][0][30:0]} : falu_res[0];
        end
        else
        begin
          wr_data[0] |= (sel_in[0][0][31] & ~a_zero[0]) ? {~sel_in[0][0][31], sel_in[0][0][30:0]} : ((falu_res[1][31] & ~feq[0]) ? falu_res[0] : sel_in[0][0]);
        end
        for (int i = 1; i < ISIZE; i++)
        begin
          wr_data[i] |= wr_data[0];
        end
      end
    dec_replic:
      begin
        if (a_nan[0])
        begin
          wr_data[0] |= sel_in[0][0];
        end
        else if (b_nan[0])
        begin
          wr_data[0] |= (sel_in[0][0][31] & ~a_zero[0]) ? falu_res[2] : falu_res[0];
        end
        else
        begin
          wr_data[0] |= (sel_in[0][0][31] & ~a_zero[0]) ? falu_res[2] : ((falu_res[1][31] & ~feq[0]) ? falu_res[0] : sel_in[0][0]);
        end
        for (int i = 1; i < ISIZE; i++)
        begin
          wr_data[i] |= wr_data[0];
        end
      end
`ifndef ACT_HAS_ALU1
    dec_shv:
      begin
        wr_data |= shv_in;
      end
    dec_shc:
      begin
        for (int i = 0; i < ISIZE-1; i++)
        begin
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Reviewed
          wr_data[i] |= rd_data[0][i+1];
// spyglass enable_block SelfDeterminedExpr-ML
        end
        wr_data[ISIZE-1] |= '0;
      end
    dec_shrc:
      begin
        for (int i = 0; i < ISIZE-1; i++)
        begin
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Reviewed
          wr_data[i+1] |= rd_data[0][i];
// spyglass enable_block SelfDeterminedExpr-ML
        end
        wr_data[0] |= '0;
      end
`endif
    dec_getid:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= {24'h0,slc_id};
        end
      end
    dec_strv:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= 32'(VID);
        end
      end
    dec_strc:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= 32'(i);
        end
      end
    dec_movf:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= state_r[i] ? 32'h1 : '0;
        end
      end
    dec_andf:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          state_i[i] = state_r[i] & rd_data[0][i][0];
          wr_data[i] |= {31'b0, state_i[i]};
        end
        state_dec = 1'b1;
      end
    dec_orf:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          state_i[i] = state_r[i] | rd_data[0][i][0];
          wr_data[i] |= {31'b0, state_i[i]};
        end
        state_dec = 1'b1;
      end
    dec_xorf:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          state_i[i] = state_r[i] ^ rd_data[0][i][0];
          wr_data[i] |= {31'b0, state_i[i]};
        end
        state_dec = 1'b1;
      end
`ifndef ACT_HAS_ALU1
    dec_lutq1, dec_exp1, dec_recip1, dec_rsqrt1:
      begin
        wr_data     |= lut_res;
        lut_wq      = 1'b1;
      end  
`endif  // ACT_HAS_ALU1
    dec_faddf, dec_fsubf, dec_frsubf:
      begin
        wr_data     |= falu_res;
        state_dec   = 1'b1;
      end
`ifndef ACT_HAS_ALU1
    dec_frelu,
`endif
    dec_fmax, dec_fmaxf, dec_fmin, dec_fminf,
    dec_rminc, dec_rminv, dec_rmaxc, dec_rmaxv:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          state_i[i] = add_neg[i] & ~feq[i];
          if (a_nan[i])
          begin
            state_i[i] = 1'b0;          // return false
            wr_data[i] |= sel_in[1][i];  // choose b
          end
          else if (b_nan[i])
          begin
            state_i[i] = 1'b1;          // return true
            wr_data[i] |= sel_in[0][i];  // choose a
          end
          else
          begin
            wr_data[i] |= state_i[i] ? sel_in[0][i] : sel_in[1][i];
          end
        end
        state_dec = (fu_inst.opc.a != dec_fmax && 
`ifndef ACT_HAS_ALU1
                     fu_inst.opc.a != dec_frelu &&
`endif
                     fu_inst.opc.a != dec_fmin);
        red_state_out = state_i;
      end
    dec_frelun, dec_frelunf:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          if (b_nan[i])
          begin
            // right bound is nan, return 0 or input
            state_i[i] = ~a_nan[i];
            wr_data[i] |= ((sel_in[0][i][31] & ~a_zero[i]) | a_nan[i]) ? '0 : sel_in[0][i];
          end
          else if (a_nan[i])
          begin
            // input is nan, return 0 or b
            state_i[i] = 1'b0;
            wr_data[i] |= (sel_in[1][i][31] & ~b_zero[i]) ? '0 : sel_in[1][i];
          end
          else
          begin
            state_i[i] = (sel_in[0][i][31] & ~a_nan[i] & ~a_zero[i]) | ~(add_neg[i] | feq[i]);
            if (add_neg[i] & ~feq[i])
              wr_data[i] |= (sel_in[0][i][31] & ~a_zero[i]) ? '0 : sel_in[0][i];
            else
              wr_data[i] |= (sel_in[1][i][31] & ~b_zero[i]) ? '0 : sel_in[1][i];
          end
        end
        state_dec = (fu_inst.opc.a == dec_frelunf);
      end
    dec_fgt, dec_flt:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= sel_in[0][i];
          if (a_nan[i])
            // a is nan, return false
            state_i[i] = 1'b0;
          else if (b_nan[i])
            // b is nan, return true
            state_i[i] = 1'b1;
          else
            state_i[i] = add_neg[i] & ~feq[i];
        end
        state_dec = 1'b1;
      end
    dec_fgte, dec_flte:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= sel_in[0][i];
          if (a_nan[i])
            // a is nan, return false
            state_i[i] = 1'b0;
          else if (b_nan[i])
            // b is nan, return true
            state_i[i] = 1'b1;
          else
            state_i[i] = add_neg[i] | feq[i];
        end
        state_dec = 1'b1;
      end
    dec_feq:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= sel_in[0][i];
          state_i[i] = feq[i];
        end
        state_dec = 1'b1;
      end
    dec_fneq:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= sel_in[0][i];
          state_i[i] = ~feq[i];
        end
        state_dec = 1'b1;
      end
    dec_fabs:
      begin
        // just make sure the sign bit is 0
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= {1'b0,sel_in[0][i][30:0]};
        end
      end
    dec_asr, dec_lsr:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= shift_out[i][31+:32];
        end
      end
    dec_sl:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= shift_out[i][32+:32];
        end
      end
    default:
      //    dec_add, dec_sub, dec_rsub, dec_abs
      begin
        wr_data     |= add_sum;
      end
    endcase // case (fu_inst.opc.a)

    //  update state
    state_nxt = '0;
    case (fu_inst.opc.a) 
    dec_rmaxv, dec_rminv:
      begin
        state_nxt = red_state_in;
      end
    dec_rmaxc, dec_rminc:
      begin
        for (int i = 0; i < ISIZE/2; i++)
        begin
          state_nxt[2*i+0] = state_i[i];
          state_nxt[2*i+1] = ~state_i[i];
        end
      end
    dec_faddf,dec_fsubf, dec_frsubf:
      begin
        // set state to true if result >= 0
        for (int i = 0; i < ISIZE; i++)
        begin
          state_nxt[i] = ~falu_res[i][31];
        end
      end
    default:
      // dec_gte, dec_lt, dec_gt, dec_lte, dec_eq, dec_neq, dec_fgte, dec_flt, dec_fgt, dec_flte, dec_feq, dec_fneq, dec_fmax, dec_fmin, dec_frelunf, dec_andf, dec_orf, dec_xorf:
      begin
        state_nxt = state_i;
      end
    endcase // case (fu_inst.opc.a)
    // set state from fu_in
    if (in_state_en)
    begin
      state_nxt = in_state;
    end
  end : alu_dp_out_PROC

  
  //
  // Registers
  //
  // outputs: state_r
  assign state_en = in_state_en | (state_dec & fu_valid & ~stall);
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1)
    begin
      state_r  <= '0;
    end
    else if (state_en)
    begin
      state_r  <= state_nxt;
    end
  end : reg_PROC             

`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_state_en;
  @(posedge clk) disable iff (rst_a !== 1'b0) (state_dec & fu_valid & ~stall) |-> (~in_state_en);
  endproperty : prop_state_en
  a_state_en: assert property (prop_state_en) else $fatal(1, "Error: state cannot be updated by ALU and IN at the same time. Check micro-code");
`endif

endmodule : npu_gtoa_fu_alu
