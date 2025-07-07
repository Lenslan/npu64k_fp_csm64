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
 * This module implements the MUL functional unit
 * Stages:
 * 1: read operands
 * 2: 32*16 mul
 * 3: accumulate
 * 4: shift&round
 * 5: write-back
 */
module npu_gtoa_fu_mul
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int ID = 0                              // MUL
    )
  (
   input  logic                       clk,            // clock
   input  logic                       rst_a,          // asynchronous reset, active high
   // instruction
   input  logic                       fu_valid,       // instruction valid per functional unit
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  act_dec_inst_t              fu_inst,        // instruction to be executed per functional units
// spyglass enable_block W240
   // two register read interfaces
   input  ixacc_t        [1:0]        rd_data,        // read data
   // one register write interface
   output act_ot_t                    wr_typ,         // write operand type
   output logic          [2:0]        wr_ad,          // write operand address
   output ixacc_t                     wr_data,        // write data
   // input from LUT
   output logic            [1:0]      q_in_accept,   // lut queue accept
   input  ix_fplut_queue_t [1:0]      q_in_data,    // lut queue data
   // flow control
   input  logic                       stall           // stall
   );
  // local wires
  logic                           wr_val_r;       // output valid, delay line
  logic                           wr_val_nxt;     // valid next cycle
  act_ot_t                        wr_typ_r;       // write register type, delay line
  act_ot_t                        wr_typ_nxt;     // write register type, next
  logic         [2:0]             wr_ad_r;        // output register address, delay line
  logic         [2:0]             wr_ad_nxt;      // output register address, next
  logic                           wr_en;          // write enable
  logic         [ISIZE-1:0][31:0] int_data;       // normalized data
  logic         [1:0]             rq;             // pop from queue
  ixacc_t                         mpy_a;          // multiplier input a
  ixacc_t                         mpy_b;          // multiplier input b
  ixacc_t                         mpy_z;          // multiplier output
  ixacc_t                         add_z;          // adder output
  ixacc_t                         add_zi;         // adder output internal
  // intermediate product register
  ixacc_t                         prod_r;
  ixacc_t                         prod_nxt;
  // intermediate registers for MAC operations
  ixacc_t                         bias_r;
  ixacc_t                         bias_nxt;
  act_lut_cmd_t [ISIZE-1:0][1:0]  cmd_r;
  act_lut_cmd_t [ISIZE-1:0][1:0]  cmd_nxt;
  logic         [ISIZE-1:0][7:0]  ex_rpl_r;
  logic         [ISIZE-1:0][7:0]  ex_rpl_nxt;
  act_dec_mpy_t                   opc_r;

  
  //
  // simple assignments to outputs
  //
  assign wr_typ       = wr_val_r ? wr_typ_r : ot_no;
  assign wr_ad        = wr_ad_r;
  assign q_in_accept  = wr_en ? rq : 2'd0;
  assign wr_val_nxt   = (wr_val_r & stall) | (fu_valid & ~stall);
  assign wr_typ_nxt   = fu_inst.fmt[0];
  assign wr_ad_nxt    = fu_inst.ops[0];
  assign wr_en        = fu_valid & ~stall;


  //
  // Select multiplier b operand
  //
  // output: rq, ex_rpl_nxt, cmd_nxt, bias_nxt, mpy_b
  always_comb
  begin : bsel_PROC
    // default outputs
    rq        = 2'b00;
    bias_nxt  = '0;
    // data pipe
    for (int i = 0; i < ISIZE; i++)
    begin
      logic           s1;
      logic [22:0]    m1;
      logic [7:0]     e1;
      logic           all_1s;
      logic           all_0s;
      logic [3:0]     e1_msb;
      ex_rpl_nxt[i] = q_in_data[1][i].exp_offset;
      all_1s =  &rd_data[1][i][14:10]; //rd_data[1][i][14:10] == 5'h1f
      all_0s = ~|rd_data[1][i][14:10]; //rd_data[1][i][14:10] == 5'h00
      case (fu_inst.opc.m)
      dec_mpyh:
        begin
          // second input operand also from input
          s1           = rd_data[1][i][15];
          if (~(all_0s|all_1s)) //not all_0s/all_1s
          begin
            e1_msb       = rd_data[1][i][14] ? 4'b1000 : 4'b0111;
            e1           = {e1_msb, rd_data[1][i][13:10]};
            //e1           = rd_data[1][i][14:10] + 8'd112;
            m1           = {rd_data[1][i][9:0], 13'b0};
          end
          else if (all_0s)
          begin
            e1           = '0;
            m1           = '0;
          end
          else //if (all_1s)
          begin
            e1           = '1;
            m1           = '1;
          end
          cmd_nxt[i]   = cmd_normal_e;
        end
      dec_mpyb:
        begin
          // second input operand also from input
          s1           = rd_data[1][i][15];
          e1           = rd_data[1][i][14:7];
          m1           = {rd_data[1][i][6:0], 16'b0};
          cmd_nxt[i]   = cmd_normal_e;
        end
      dec_mpy:
        begin
          // second input operand also from input
          s1           = rd_data[1][i][31];
          e1           = rd_data[1][i][30:23];
          m1           = rd_data[1][i][22:0];
          cmd_nxt[i]   = cmd_normal_e;
        end
      dec_mac0:
        begin
          // second input operand from scaling queue 0
          rq           = 2'b01;
          s1           = q_in_data[0][i].mul.sgn;
          e1           = q_in_data[0][i].mul.ex;
          m1           = q_in_data[0][i].mul.mant;
          bias_nxt[i]  = {q_in_data[0][i].ofs.sgn, q_in_data[0][i].ofs.ex, q_in_data[0][i].ofs.mant, 8'd0};
          cmd_nxt[i]   = cmd_normal_e;
        end
      default: // dec_mac1
        begin
          // second input operand from scaling queue 1
          rq           = 2'b10;
          s1           = q_in_data[1][i].mul.sgn;
          e1           = q_in_data[1][i].mul.ex;
          m1           = q_in_data[1][i].mul.mant;
          bias_nxt[i]  = {q_in_data[1][i].ofs.sgn, q_in_data[1][i].ofs.ex, q_in_data[1][i].ofs.mant, 8'd0};
          // replicate exponent
          cmd_nxt[i]   = q_in_data[1][i].command;
        end
      endcase // case (fu_inst.opc.m)
      // set multiplier input
      mpy_b[i] = {s1, e1, m1};
    end // for (int i = 0; i < ISIZE; i++)
  end : bsel_PROC
  

  //
  // FP multiplier
  //
  for (genvar gi = 0; gi < ISIZE; gi++)
  begin : fpmpy_GEN
    npu_fp_mpy
    u_fp_mpy_inst
     (
      .a      ( rd_data[0][gi] ),
      .b      ( mpy_b[gi]      ),
      .z      ( prod_nxt[gi]   )
     );
  end : fpmpy_GEN

  
  //
  // FP adder
  //
  for (genvar gi = 0; gi < ISIZE; gi++)
  begin : fpadd_GEN
    npu_fp_add
    u_fp_add_inst
     (
      .a      ( prod_r[gi]  ),
      .b      ( bias_r[gi]  ),
      .z      ( add_zi[gi]  )
     );
     assign add_z[gi] = ((opc_r == dec_mac0) || (opc_r == dec_mac1)) ? add_zi[gi] : prod_r[gi];
  end : fpadd_GEN

  
  //
  // Second stage output result
  //
  // outputs: wr_data
  always_comb
  begin : add_PROC
    for (int i = 0; i < ISIZE; i++)
    begin
      logic [9:0] e;
      // get adder output
      wr_data[i] = add_z[i];
      // offset on exponent
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      e = {2'b00,wr_data[i][30:23]} + {{2{ex_rpl_r[i][7]}},ex_rpl_r[i]};
// spyglass enable_block W164a
// spyglass disable_block W263
// SMD: Case Selector width mismatch
// SJ: Reviewed
      case (cmd_r[i])
      cmd_nan_e: 
        begin
          // nan
          wr_data[i][30:0] = '1;
        end
      cmd_exp_repl_e:
        begin
          // replace exp
          if (e[9] || (e[8:0] == '0))
          begin
            // underflow
            wr_data[i][30:0] = '0;
          end
          else if (e[8] || (e[7:0] == '1))
          begin
            // overflow
            wr_data[i][30:0] = '1;
          end
          else
          begin
            wr_data[i][30:23] = e[7:0];
          end
        end
      cmd_exp_repl_neg_e:
        begin
          // replace exp with ~sign
          wr_data[i][31] = ~add_z[i][31];
          // replace exp
          if (e[9] || (e[8:0] == '0))
          begin
            // underflow
            wr_data[i][30:0] = '0;
          end
          else if (e[8] || (e[7:0] == '1))
          begin
            // overflow
            wr_data[i][30:0] = '1;
          end
          else
          begin
            wr_data[i][30:23] = e[7:0];
          end
        end            
      default:
        begin
          wr_data = wr_data;
        end
      endcase // case (cmd_r)
// spyglass enable_block W263
    end // for (int i = 0; i < ISIZE; i++)
  end : add_PROC


  //
  // registers between 1st stage and 2nd stage
  //
  // outputs: wr_val_r, wr_typ_r, wr_ad_r, prod_r, bias_r, cmd_r, ex_rpl_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1)
    begin
      wr_val_r <= 1'b0;
      wr_typ_r <= ot_no;
      wr_ad_r  <= '0;
      prod_r   <= '0;
      bias_r   <= '0;
      cmd_r    <= cmd_normal_e;
      ex_rpl_r <= '0;
      opc_r    <= dec_mpyh;
    end
    else
    begin
      wr_val_r     <= wr_val_nxt;
      if (wr_en)
      begin
        // write-back controls
        wr_typ_r <= wr_typ_nxt;
        wr_ad_r  <= wr_ad_nxt;
        // results from partial multiplication
        prod_r   <= prod_nxt;
        bias_r   <= bias_nxt;
        cmd_r    <= cmd_nxt;
        ex_rpl_r <= ex_rpl_nxt;
        opc_r    <= fu_inst.opc.m;
      end
    end
  end : reg_PROC
  
  
endmodule : npu_gtoa_fu_mul
