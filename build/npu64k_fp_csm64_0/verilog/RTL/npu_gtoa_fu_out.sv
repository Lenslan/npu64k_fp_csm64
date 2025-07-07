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
 * This module implements the output functional unit
 * the module:
 * - adds an asymmetric quantization offset
 * - pushes the data to the output
 */


module npu_gtoa_fu_out
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                       clk,           // clock
   input  logic                       rst_a,         // asynchronous reset, active high
   // instruction
   input  logic                       fu_valid,      // instruction valid per functional unit
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  act_dec_inst_t              fu_inst,       // instruction to be executed per functional units
// spyglass enable_block W240
   // two register read interfaces
   input  ixacc_t        [1:0]        rd_data,       // read data
   // hlapi sat and pool parameters
   input  logic                       cf_fm,         // feature-map output
   input  logic                       cf_sat,        // saturation enable
   input  logic                       cf_dbl,        // 16b output
   input  fmode_t                     cf_fmode,      // float mode (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8)
   // streaming output
   output logic                       out_valid,     // output data valid
   input  logic                       out_accept,    // accept output data
   output ixacc_t                     out_data,      // input data
   output logic                       out_dbl,       // 16b output
   // flow control
   output logic                       busy,          // busy flag
   output logic                       ostall,        // stall output
   input  logic                       stall          // stall input
   );
  // internal floating-point representation
  typedef struct packed {
    logic        s;   // sign bit
    logic        n;   // NaN if true
    logic        z;   // zero if true
    logic [23:0] m;   // mantissa with explicit leading 1
    logic [7:0]  e;   // exponent with bias 127
  } sfp_t;

  // local state
  logic                               done_r;        // asserted when write is done during stall
  logic                               done_nxt;      // next state

  sfp_t   [ISIZE-1:0]                 fp_scale_in;   // input to floating-point scaling
  logic   [ISIZE-1:0][31:0]           fp_scale_out;  // result from floating-point scaling
  logic   [ISIZE-1:0][31:0]           fp_rnd;        // rounded FP result
  ixacc_t                             int32_data;    // output of fp to int32 converter
  ixacc_t                             int_data;      // integer output data
  logic   [ISIZE-1:0][31:0]           pres_a;        // prescale input a
  logic   [ISIZE-1:0][7:0]            pres_b;        // prescale input b
  logic   [ISIZE-1:0][31:0]           pres_z;        // prescale output

  
  // optimized 27b count leading zero bits
  function automatic logic [4:0] clz26(logic [25:0] t);
    logic [31:0]     i;
    logic [4:0]      e;
    logic [3:0]      v;
    logic [4:0][2:0] l;
    // extend lsb by 1 to 32b
    i = {t, 6'b111111};
    // decode in 4 chunks of 8b    
    for (int c = 0; c < 4; c++)
    begin
      v[c] = i[8*c+:8] != '0;
      (* full_case, parallel_case *)
      casez (i[8*c+:8])
      8'b01??????: l[c] = 3'd1;
      8'b001?????: l[c] = 3'd2;
      8'b0001????: l[c] = 3'd3;
      8'b00001???: l[c] = 3'd4;
      8'b000001??: l[c] = 3'd5;
      8'b0000001?: l[c] = 3'd6;
      8'b00000001: l[c] = 3'd7;
      default:     l[c] = 3'd0;
      endcase // casez (i[8*c+:8])
    end
    (* full_case, parallel_case *)
    casez (v)
    4'b1???: e = {2'b00, l[3]};
    4'b01??: e = {2'b01, l[2]};
    4'b001?: e = {2'b10, l[1]};
    default: e = {2'b11, l[0]};
    endcase // casez (v)
    return e;
  endfunction : clz26


  // simple assignments
  assign out_dbl = cf_dbl;

  // track if write is done during stall
  assign done_nxt = ((out_valid & out_accept) | done_r) & stall;
  // outputs: done_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : done_reg_PROC
    if (rst_a == 1'b1)
    begin
      done_r <= 1'b0;
    end
    else 
    begin
      done_r <= done_nxt;
    end
  end : done_reg_PROC


  //
  // Select floating-point feature-map input
  //
  // output: fp_scale_in
  always_comb
  begin : fpin_sel_PROC
    for (int i = 0; i < ISIZE; i++)
    begin
      fp_scale_in[i].s = rd_data[0][i][31];
      fp_scale_in[i].n = rd_data[0][i][30:23] == 8'hff;
      fp_scale_in[i].z = rd_data[0][i][30:23] == 8'h00;
      fp_scale_in[i].m = {1'b1, rd_data[0][i][22:0]};
      fp_scale_in[i].e = rd_data[0][i][30:23];
    end
  end : fpin_sel_PROC

  
  //
  // Post-scaler operand selection
  //
  // outputs: pres_a, pres_b
  always_comb
  begin : presel_PROC
    for (int i = 0; i < ISIZE; i++)
    begin
      acc_t             src1;
      src1 = fu_inst.fmt[2] == ot_no ? 32'h0000007c : rd_data[1][i];
      pres_a[i] = {fp_scale_in[i].s, fp_scale_in[i].e, fp_scale_in[i].m[22:0]};
      pres_b[i] = src1[7:0];
    end
  end : presel_PROC

  
  //
  // FP prescale
  //
  for (genvar gi = 0; gi < ISIZE; gi++)
  begin : pres_GEN
    npu_fp_prescale
    u_out_prescale_inst
     (
      .a      ( pres_a[gi]   ),
      .b      ( pres_b[gi]   ),
      .z      ( pres_z[gi]   )
     );
  end : pres_GEN


  //
  // Floating-point multiply result
  //
  // output: fp_scale_out
  always_comb
  begin : scale_PROC
    for (int i = 0; i < ISIZE; i++)
    begin
      fp_scale_out[i][31] = fp_scale_in[i].s;
      if (fp_scale_in[i].n | (pres_z[i][30:23] == '1))
      begin
        fp_scale_out[i][30:0] = '1;
      end
      else if (fp_scale_in[i].z | (pres_z[i][30:23] == '0))
      begin
        fp_scale_out[i][30:0] = '0;
      end
      else
      begin
        fp_scale_out[i][30:23] = pres_z[i][30:23];
        fp_scale_out[i][22:0]  = pres_z[i][22:0];
      end
    end // for (int i = 0; i < ISIZE; i++)
  end : scale_PROC
  

  //
  // FP to integer
  //
  for (genvar gj = 0; gj < ISIZE; gj++)
  begin : toint_GEN
    npu_fp_ftoi
    #(
      .rnd_mode(1) // convergent
    )
    u_toint_inst
      (
      .a      ( fp_scale_out[gj]   ),
      .z      ( int32_data[gj]     )
       );
  end : toint_GEN
  
  
  //
  // Integer conversion
  //
  always_comb
  begin : toint_PROC
    if (fu_inst.opc.o != dec_pushout)
    begin
      // only for floating-point fpushout
      int_data = int32_data;
    end
    else
    begin
      // int pushout
      int_data = rd_data[0];
    end
    // saturate
    for (int i = 0; i < ISIZE; i++)
    begin
      logic [7:0]  asym;
      logic [32:0] int_data_tmp;
      asym = ((fu_inst.fmt[2] == ot_no) || ~cf_fm || cf_dbl) ? 8'h00 : rd_data[1][i][15:8];
      // asymmetric quantization
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      int_data_tmp = {int_data[i][31], int_data[i]} + {{25{asym[7]}}, asym};
// spyglass enable_block W164a
      int_data[i] = int_data_tmp[31:0];
      if (cf_sat && cf_fm)
      begin
        if (cf_dbl)
        begin
          //if (int_data_tmp > 33'sh00007fff)
          if ((~int_data_tmp[32]) & (|int_data_tmp[31:15]))
          begin
            int_data[i] = 32'h00007fff;
          end
          //else if (int_data_tmp < 33'shffff8000)
          else if ((int_data_tmp[32]) & (~&int_data_tmp[31:15]))
          begin
            int_data[i] = 32'hffff8000;
          end
        end
        else
        begin
          //if (int_data_tmp > 33'sh0000007f)
          if ((~int_data_tmp[32]) & (|int_data_tmp[31:7]))
          begin
            int_data[i] = 32'h0000007f;
          end
          //else if (int_data_tmp < 33'shffffff80)
          else if ((int_data_tmp[32]) & (~&int_data_tmp[31:7]))
          begin
            int_data[i] = 32'hffffff80;
          end
        end
      end
    end
  end : toint_PROC


  //
  // Rounding for floating-point conversions
  //
  // outputs: fp_rnd
  always_comb
  begin : fp_rnd_PROC
    logic [33:0]            inc;    // ov[2],exp[8],nov[1],mnt[23]
    logic                   clr16;  // bf16 convergent rounding clear bit 16
    logic                   clr13;  // fp16 convergent rounding clear bit 13
    logic [ISIZE-1:0][33:0] res;    // internal result
    inc = '0;
    if (cf_fmode == fmode_fp16_e)
    begin
      inc[33:28] |= -7;    // adjust exponent bias when convering to FP16
      inc[12]    |= 1'b1;  // bit 12 is 1/2 lsb
    end
    else
    begin
      inc[15]    |= 1'b1;  // bit 15 is 1/2 lsb
    end
    for (int i = 0; i < ISIZE; i++)
    begin
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      res[i]     = {2'b00,pres_z[i][30:23],1'b1,pres_z[i][22:0]} + inc;
// spyglass enable_block W164a
      clr16      = inc[15] & pres_z[i][15] & (pres_z[i][14:0] == '0);
      clr13      = inc[12] & pres_z[i][12] & (pres_z[i][11:0] == '0);
      res[i][16] = res[i][16] & ~clr16;
      res[i][13] = res[i][13] & ~clr13;
      fp_rnd[i][31] = fp_scale_in[i].s;
      if (res[i][33] || (res[i][32:24] == '0) || fp_scale_in[i].z)
      begin
        // zero
        fp_rnd[i][30:0] = '0;
      end
      else if (res[i][32] || (res[i][31:24] == '1) || fp_scale_in[i].n)
      begin
        // exponent overflow
        fp_rnd[i][30:0] = '1;
      end
      else if (res[i][23])
      begin
        // no overflow into exponent
        fp_rnd[i][30:0] = {res[i][31:24],res[i][22:0]};
      end
      else
      begin
        // overflow into exponent from rounding
        fp_rnd[i][30:0] = {res[i][31:24],1'b0,res[i][22:1]};
      end
    end
  end : fp_rnd_PROC

  
  //
  // output data
  //
  always_comb
  begin : out_PROC
    out_data = '0;
    if (fu_inst.opc.o != dec_pushout)
    begin
      // integer output
      case (cf_fmode)
      fmode_int32_e:
        begin
          // fp32 -> int32
          for (int i = 0; i < ISIZE; i++)
          begin
            out_data[i] = int_data[i];
          end
        end
      fmode_fp16_e:
        begin
          // fp32 -> fp16
          for (int i = 0; i < ISIZE; i++)
          begin
            logic [9:0] ex;
            out_data[i][15]    = fp_rnd[i][31];     // sign
            out_data[i][14:10] = fp_rnd[i][27:23];  // exponent
            out_data[i][9:0]   = fp_rnd[i][22:13];  // mantissa
            if ((fp_rnd[i][30:28] != '0) || (fp_rnd[i][27:23] == '1))
            begin
              // value too big, set to nan
              out_data[i][14:0] = '1;
            end
            else
            begin
              // normal output
            end
          end
        end
      fmode_bf16_e:
        begin
          // fp32 -> bf16
          for (int i = 0; i < ISIZE; i++)
          begin
            out_data[i][15:0] = fp_rnd[i][31:16];
          end
        end
      default: // fmode_fp32_e:
        begin
          // fp32 -> fp32
          for (int i = 0; i < ISIZE; i++)
          begin
            out_data[i] = fp_scale_out[i];
          end
        end
      endcase // case (cf_fmode)
    end // if (fu_inst.opc.o != dec_pushout)    
    else
    begin
      out_data = int_data;
    end // else: !if(fu_inst.opc.o != dec_pushout)
  end : out_PROC
  
  
  // assign outputs
  assign busy       = 1'b0;
  assign ostall     = fu_valid & (~out_accept) & (~done_r);
  assign out_valid  = fu_valid & ~done_r;
  
endmodule : npu_gtoa_fu_out
