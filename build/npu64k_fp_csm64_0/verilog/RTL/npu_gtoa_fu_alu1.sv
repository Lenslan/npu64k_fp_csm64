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
// vcs -sverilog +incdir+$NPU_HOME/build/verilog/RTL -y $NPU_HOME/build/verilog/RTL +libext+.sv+.v $NPU_HOME/build/verilog/RTL/npu_types.sv $NPU_HOME/build/verilog/RTL/npu_gtoa_types.sv npu_gtoa_fu_alu1.sv npu_gtoa_fu_alu_lut.sv

module npu_gtoa_fu_alu1
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                                       clk,           // clock
   input  logic                                       rst_a,         // asynchronous reset, active high
   // instruction
   input  logic                                       fu_valid,      // instruction valid per functional unit
// spyglass disable_block W240
//SMD:Unread input
//SJ :Macro defined packed signal can be ignore
   input  act_dec_inst_t                              fu_inst,       // instruction to be executed per functional units
// spyglass enable_block W240
   // three register read interfaces
   input  ixacc_t                                     rd_data,       // read data
   // spatial shift and broadcast interface
   input  ixacc_t                                     shv_in,        // shv input
   input  ixacc_t                                     bcv_in,        // spatial broadcast input
   // one register write interface
   output act_ot_t                                    wr_typ,        // write operand type
   output logic             [2:0]                     wr_ad,         // write operand address
   output ixacc_t                                     wr_data,       // write data
   input  logic             [ISIZE-1:0]               alu_state,     // ALU state to ALU1
   // LUT table
   input  act_lutt_t                                  lut_data,
   // queue  interface, no back-pressure, compile should have scheduled correctly
   output logic             [1:0]                     q_in_valid,    // lut queue valid
   output ix_fplut_queue_t  [1:0]                     q_in_data,     // lut queue data
   // flow control
   input  logic                                       stall          // stall
   );
  // local wires
  logic                               lut_wq;        // look-up table queue write data
  ixacc_t                             lut_res;       // look-up table result
  
  
  // simple assignments
  assign wr_typ     = fu_valid ? fu_inst.fmt[0] : ot_no;
  assign wr_ad      = fu_inst.ops[0];
  assign q_in_valid = (fu_valid & ~stall) ? {2{lut_wq}} : 2'b00;  

  
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
   .rd_data       ( rd_data       ),
   .res           ( lut_res       ),
   .q_data        ( q_in_data     )
  );

  
  //
  // ALU output selection
  //
  // outputs: wr_data, lut_wq
  always_comb
  begin : alu_dp_out_PROC
    // default outputs
    lut_wq  = 1'b0;
    wr_data = '0;
    case (fu_inst.opc.a) 
    dec_bcv:
      begin
        wr_data |= bcv_in;
      end
    dec_bcc:
      begin
        wr_data |= {ISIZE{rd_data[0]}};
      end
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
          wr_data[i] |= rd_data[i+1];
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
          wr_data[i+1] |= rd_data[i];
// spyglass enable_block SelfDeterminedExpr-ML
        end
        wr_data[0] |= '0;
      end
    dec_selecth:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          logic [15:0] d;
          d = alu_state[i] ? rd_data[i][31:16] : rd_data[i][15:0];
          wr_data[i][31] |= d[15];
          case (d[14:10])
          5'h00:
            begin
              // zero
              wr_data[i][30:23] |= 8'h00;
            end
          5'h1f:
            begin
              // nan
              wr_data[i][30:23] |= 8'hff;
              wr_data[i][22:13] |= d[9:0];
            end
          default:
            begin
              wr_data[i][30:23] |= {3'd0,d[14:10]} + 8'd112;
              wr_data[i][22:13] |= d[9:0];
            end
          endcase // case (d[14:10])
        end
      end // case: dec_selecth
    dec_selectb:
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i][31:16] |= alu_state[i] ? rd_data[i][31:16] : rd_data[i][15:0];
        end
      end
    dec_lutq1, dec_exp1, dec_recip1, dec_rsqrt1:
      begin
        // LUT1
        wr_data    |= lut_res;
        lut_wq      = 1'b1;
      end  
    default: // dec_frelu, wdata ignored for lut0,exp0,recip0,rsqrt0 instructions
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          if (rd_data[i][30:23] == '0)
          begin
            // zero input, keep sign bit
            wr_data[i][31] |= rd_data[i][31];
          end
          else if (~(rd_data[i][31] | (&rd_data[i][30:23])))
          begin
            // positive, non-NaN
            wr_data[i] |= rd_data[i];
          end
        end     
      end
    endcase // case (fu_inst.opc.a)
  end : alu_dp_out_PROC

endmodule : npu_gtoa_fu_alu1
