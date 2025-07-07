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
// Two cycle functions, process ISIZE/2 per cycle
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv npu_gtoa_types.sv npu_gtoa_fu_alu_lut.sv -y $SYNOPSYS/dw/sim_ver +libext+.v
//

module npu_gtoa_fu_alu_lut
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   // clock and reset
   input  logic                                 clk,
   input  logic                                 rst_a,
   // input controls and data
   input  logic                                 valid,          // valid instruction
   input  logic                                 stall,          // stall pipeline
   input  act_lutt_t                            lut_data,       // look-up table
   input  act_dec_alu_t                         opc,            // instruction opcode
   input  ixacc_t                               rd_data,        // input data, stable throughout sequence
   // result input and output
   output ixacc_t                               res,            // (partial) result output
   output ix_fplut_queue_t  [1:0]               q_data
   );
  // local wires
  act_lutt_t                                     lut_data_eff; // effective LUT
  act_e8m23_t            [ISIZE/2-1:0]           lut_in;       // muxed input data
  acc_t                  [ISIZE/2-1:0]           lut_out;      // LUT write data
  acc_t                  [ISIZE/2-1:0]           res_r;        // LUT write data keep
  logic                                          q_en;         // enable lut data register
  act_fp_lut_mul_queue_t [1:0][ISIZE/2-1:0]      q_r;          // LUT result register
  act_fp_lut_mul_queue_t [1:0][ISIZE/2-1:0]      q_out;        // 1/2 of the LUT results

  
  ////////////////////////////////////////////////////
  //
  // Hardwired LUT tables
  //
  ////////////////////////////////////////////////////
  
  // exponent table
  // we only care about the exponent values <=0
  // the positive portion of the table should be all zero
  const act_lut_half_t exp_table_data = {
                                         {12'h821,24'h3a2ea9,24'h3c2d2c,24'h3d2c8e}
                                         ,{12'h815,24'h3bbf39,24'h3d83ea,24'h3e3b25}
                                         ,{12'h80e,24'h3ca20c,24'h3e2c98,24'h3ec154}
                                         ,{12'h806,24'h3d4076,24'h3ea2b8,24'h3f1531}
                                         ,{12'h800,24'h3dbefe,24'h3f0081,24'h3f4439}
                                         ,{12'h7f6,24'h3e29ca,24'h3f3356,24'h3f6722}
                                         ,{12'h7eb,24'h3e8abb,24'h3f609b,24'h3f7a4d}
                                         ,{12'h7d9,24'h3ed351,24'h3f7cdb,24'h3f7fef}
                                         ,{24'h0,24'h0}
                                         };

  // reciprocal table
  // recip is symmetric about 0, to save muxing logic, only
  // handle the positive region, pass the sign to the MUL1
  // through the output queue
  // recip makes use of the exp_offset and NaN side logic via
  // the MUL1 output queue
  const act_lut_half_t recip_table_data = {
                                           {12'h800,24'h3e1363,24'hbf530c,24'h3fc95b}
                                           ,{12'h7fd,24'h3e491e,24'hbf81d6,24'h3fdf5d}
                                           ,{12'h7fa,24'h3e85fc,24'hbf9d2a,24'h3ff5b6}
                                           ,{12'h7f8,24'h3eabf8,24'hbfb9a1,24'h400586}
                                           ,{12'h7f6,24'h3ee1ce,24'hbfde99,24'h401238}
                                           ,{12'h7f4,24'h3f1870,24'hc007fc,24'h4021a3}
                                           ,{12'h7f2,24'h3f429b,24'hc01ff4,24'h402f43}
                                           ,{12'h7f1,24'h3f683b,24'hc033f5,24'h4039e6}
                                           ,{24'h0,24'h0}
                                           };
  
  // reciprocal square-root table
  // rsqrt only has a positive region
  // rsqrt makes use of the exp_offset and NaN side logic via the
  // MUL1 output queue
  const act_lut_half_t rsqrt_table_data = {
                                           {12'h810,24'h3c7754,24'hbe3a9f,24'h3f7ccd}
                                           ,{12'h80a,24'h3cc577,24'hbe76f3,24'h3f8abd}
                                           ,{12'h806,24'h3d1c0c,24'hbea296,24'h3f9818}
                                           ,{12'h802,24'h3d7291,24'hbed3b0,24'h3fa609}
                                           ,{12'h7ff,24'h3db5d3,24'hbf06fe,24'h3fb414}
                                           ,{12'h7fa,24'h3e0bac,24'hbf2ea6,24'h3fc437}
                                           ,{12'h7f6,24'h3e4f09,24'hbf5d1c,24'h3fd43f}
                                           ,{12'h7f3,24'h3e99e1,24'hbf8c49,24'h3fe5cf}
                                           ,{24'h0,24'h0}
                                           };
    

  /////////////////////////////////////////////////////////////////////
  // Select a look up table
  /////////////////////////////////////////////////////////////////////
  // outputs: lut_data_eff
  always_comb 
  begin : lut_sel_PROC
    lut_data_eff = '0;
    case (opc)
    dec_recip0, dec_recip1:
      begin
        // pos and neg tables are the same; nan if 0
        lut_data_eff.half[0]                  = recip_table_data; 
        lut_data_eff.half[1]                  = recip_table_data; 
      end
    dec_rsqrt0, dec_rsqrt1:
      begin
        // nan if negative or 0
        lut_data_eff.half[1]                  = rsqrt_table_data; 
      end
    dec_exp0, dec_exp1:
      begin
        // output exp(0) = 1, table for negative
        lut_data_eff.half[0]                  = exp_table_data; 
        lut_data_eff.half[1].entries[0].coef0 = 24'h3f8000; // 1 if 0
        lut_data_eff.half[1].lim_offs         = 24'h3f8000; // 1 if positive
      end
    default:
      begin
        lut_data_eff                          = lut_data;
      end
    endcase // case (opc)
  end : lut_sel_PROC


  /////////////////////////////////////////////////////////////////////
  // Execute in two instructions
  /////////////////////////////////////////////////////////////////////
  always_comb
  begin : split_PROC
    if (opc == dec_lutq0 || opc == dec_exp0 || opc == dec_recip0 || opc == dec_rsqrt0)
    begin
      lut_in = rd_data[0*ISIZE/2+:ISIZE/2];
    end
    else
    begin
      lut_in = rd_data[1*ISIZE/2+:ISIZE/2];
    end
  end : split_PROC
  
  
  /////////////////////////////////////////////////////////////////////
  // Actual look-up
  /////////////////////////////////////////////////////////////////////
  always_comb
  begin : find_idx_PROC
    // initialize to 0, so we can do ORbus
    q_out   = '0;
    lut_out = '0;
    // find index
    for (int i = 0; i < ISIZE/2; i++) 
    begin
      act_lut_half_t                      h;
      logic                               sgn;
      logic          [7:0]                ex;
      logic          [ACT_LUT_SIZE/2-1:0] match;
      logic          [ACT_LUT_SIZE/2:0]   match_oh;
      // default match
      match = '0;
      // select positive or negative table
      h = '0;
      if (lut_in[i][31])
      begin
        h |= lut_data_eff.half[0];
      end
      else
      begin
        h |= lut_data_eff.half[1];
      end
      // exponent bypass for recip and rsqrt
      case (opc)
      dec_recip0, dec_recip1:
        begin
          // force exponent to 0, 127 after bias
          ex  = 8'h7f;
          sgn = 1'b0;
        end
      dec_rsqrt0, dec_rsqrt1:
        begin
          // force exponent to 0|1, 127|128 after bias
          ex = lut_in[i][23] ? 8'h7f : 8'h80;
          sgn = 1'b0;
        end
      default:
        begin
          // pass exponent
          ex  = lut_in[i][30:23];
          sgn = lut_in[i][31];
        end
      endcase
      // create temperature code
      match[0] |= (ex == '0);
      for (int j = 0; j < ACT_LUT_SIZE/2; j++)
      begin
        match[j] |= {h.entries[j].lim, 19'h0} >= {ex,lut_in[i][22:0]};
      end
      // create one-hot with msb for extrapolation --> should assert one-hot
      match_oh = {1'b1,match} & ~{match,1'b0};
      // select LUT result entry
      q_out[1][i].mul |= {sgn,ex,lut_in[i][22:0]};
      q_out[0][i].mul |= {sgn,ex,lut_in[i][22:0]};
      for (int j = 0; j < ACT_LUT_SIZE/2; j++)
      begin
        if (match_oh[j])
        begin
          q_out[1][i].ofs |= h.entries[j].coef0;  // offs
          q_out[0][i].ofs |= h.entries[j].coef1;  // offs
          lut_out[i]      |= {h.entries[j].coef2,8'h0};  // saved to rf, convert back to fp32
        end
      end
      if (match_oh[ACT_LUT_SIZE/2])
      begin
        // linear interpolation, also for NaN
        q_out[1][i].ofs |= h.lim_offs;
        q_out[0][i].ofs |= h.lim_deriv;
        lut_out[i]      |= '0;
      end
      // special logic for recip, rsqrt
      case (opc)
      dec_recip0, dec_recip1:
        begin
          q_out[1][i].exp_offset = 'd127 - lut_in[i][30:23];
          if (lut_in[i][30:23] == 8'h00 || lut_in[i][30:23] == 8'hff) 
          begin
            // NaN input or divide by 0 --> NaN 
            q_out[1][i].command = cmd_nan_e;
          end  
          else if (lut_in[i][31]) 
          begin
            // sign is set, so output should have same negative sign, replace the exp
            q_out[1][i].command = cmd_exp_repl_neg_e;
          end
          else 
          begin
            // keep the sign the same (positive), replace the exp
            q_out[1][i].command = cmd_exp_repl_e;
          end
        end
      dec_rsqrt0, dec_rsqrt1:
        begin
          q_out[1][i].exp_offset = ('d128 - lut_in[i][30:23])>>1;
          if (lut_in[i][30:23] == 8'h00 || lut_in[i][30:23] == 8'hff || lut_in[i][31] == 1'b1)
          begin
            // NaN 
            q_out[1][i].command = cmd_nan_e;
          end  
          else 
          begin
            // replace the exp 
            q_out[1][i].command = cmd_exp_repl_e;
          end        
        end
      default: 
        begin
          q_out   =  q_out;
        end
      endcase // case (opc)
    end // for (int i = 0; i < ISIZE/2; i++)
  end : find_idx_PROC
  

  //
  // Select output
  //
  // outputs: res, w_nxt
  assign res       = {lut_out, res_r};
  assign q_data[0] = {q_out[0], q_r[0]};
  assign q_data[1] = {q_out[1], q_r[1]};


  //
  // state 
  //
// spyglass disable_block STARC05-1.3.1.3
//SMD:Async reset signal other use
//SJ :rst_a(rst_dp) below and q_r used as non-reset/synchronous-reset at npu_shared_hl_ctrl_dma_mmio.sv for signal mmio_status_en
  assign q_en = (opc == dec_lutq0 || opc == dec_exp0 || opc == dec_recip0 || opc == dec_rsqrt0) & valid & ~stall; // store intermediata result for 0 instructions
  // outputs: q_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1)
    begin
      q_r   <= '0;
      res_r <= '0;
    end
    else 
    begin
      if (q_en)
      begin
        q_r   <= q_out;
        res_r <= lut_out;
      end
    end
  end : reg_PROC
// spyglass enable_block STARC05-1.3.1.3 

endmodule : npu_gtoa_fu_alu_lut
