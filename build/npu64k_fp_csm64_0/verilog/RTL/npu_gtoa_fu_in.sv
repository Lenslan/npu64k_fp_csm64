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
 * This module implements the input functional unit
 * the module:
 * - pops an input from an input stream
 * - scales down the input
 * - adds a bias

 In case of double wide inputs the module will only produce data every other cycle

vcs -sverilog $NPU_HOME/build/verilog/RTL/npu_types.sv npu_gtoa_types.sv npu_gtoa_fu_in.sv +incdir+$NPU_HOME/build/verilog/RTL tb/npu_gtoa_fu_in_tb.sv tb/npu_gtoa_fu_in_tb.o ../../../../npu_deps/SoftFloat-3e/build/Linux-386-GCC/softfloat.a -debug_all
 
  */


module npu_gtoa_fu_in
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int ID     = 0,                        // instance ID
    parameter int VID    = 0,                        // lane index
    parameter int GATHEN = 1                         // enable gather
  )
  (
   input  logic                       clk,           // clock
   input  logic                       rst_a,         // asynchronous reset, active high
   // double wide input
   input  logic                       attr_fm,       // feature-map or accumulator
   input  logic                       attr_dbl,      // double wide input
   input  fmode_t                     attr_fmode,    // float mode (0-int, 1-fp32, 2-fp16, 3-bf16, 4-fp8)
   // instruction
   input  logic                       fu_valid,      // instruction valid per functional unit
   // spyglass disable_block W240
   //SMD:Unread input
   //SJ :Packed signal fu_inst can be ignored, some bits of rd_data are not read can be ignored as well
   input  act_dec_inst_t              fu_inst,       // instruction to be executed per functional units
   // two register read interfaces
   input  ixacc_t      [1:0]          rd_data,       // read data
   // spyglass enable_block W240
   // one register write interface
   output act_ot_t                    wr_typ,        // write operand type
   output logic        [2:0]          wr_ad,         // write operand address
   output ixacc_t                     wr_data,       // write data
   // padding index
   input  offset_t     [ISIZE/4-1:0]  cidx,          // column index
   // streaming input
   input  logic                       in_valid,      // input data valid
   output logic                       in_accept,     // accept input data
   input  ixacc_t                     in_data,       // input data
   // interface for gather
   input  offset_t                    in_offs0,      // offset dimension 0
   input  offset_t                    in_offs1,      // offset dimension 1
   input  offset_t                    gather_base,   // gather base address
   input  acc_t                       rd_vr7i0,      // read data from vr7 channel 0
   input  acc_t                       rd_vr7v0l,     // read data from vr7 vector 0 low
   input  acc_t                       rd_vr7v0h,     // read data from vr7 vector 0 high
   output logic                       gather_val,    // gather valid
   input  logic                       gather_acc,    // gather accept
   output offset_t                    gather_prod,   // gather product base+offs0*v0l+offs1*v0h
   // ALU states
   output logic                       state_en,      // alu state enable
   output logic        [ISIZE-1:0]    state,         // alu state
   // parameters for padding counter update
   output logic                       padval,        // padding is enabled
   input  logic        [ISIZE/4-1:0]  padflag,       // data is padded
   output logic                       padacc,        // update padding
   input  logic                       it_first,      // iterator first flag
   // flow control
   output logic                       ostall,        // stall output
   input  logic                       stall          // stall input
   );

  // local wires
  logic                              tgl_r;             // even/odd toggle
  logic                              tgl_nxt;           // next toggle value
  logic                              data_en;           // enable data register
  ixacc_t                            data_r;            // first data
  logic         [ISIZE-1:0][47:0]    dataw;             // data expanded to 48b
  logic         [ISIZE-1:0][31:0]    fp_scale_in;       // input to floating-point scaling
  logic         [ISIZE-1:0][31:0]    fp_scale_out_tmp;  // result from floating-point scaling
  logic         [ISIZE-1:0][31:0]    fp_scale_out_nxt;  // result from floating-point scaling
  logic         [ISIZE-1:0][31:0]    fp_scale_out_r;    // result from floating-point scaling reg
  logic         [ISIZE-1:0][31:0]    fp_bias_in;        // input to floating-point bias
  logic         [ISIZE-1:0][31:0]    fp_bias_out;       // result from biasing
  act_dec_in_t                       opc_r;             // opcode
  act_ot_t                           fmt_r;             // optype
  logic                              state_en_r;        // state enable
  logic                              state_en_nxt;      // state enable next
  logic                              wr_val_r;          // output valid, delay line
  logic                              wr_val_nxt;        // valid next cycle
  act_ot_t                           wr_typ_r;          // write register type, delay line
  act_ot_t                           wr_typ_nxt;        // write register type, next
  logic         [2:0]                wr_ad_r;           // output register address, delay line
  logic         [2:0]                wr_ad_nxt;         // output register address, next
  logic                              wr_en;             // write enable
  logic         [ISIZE/4-1:0][4:0]   ucntr_r;           // unpadded pixel counter
  logic         [ISIZE/4-1:0][4:0]   ucntr_nxt;         // unpadded pixel counter next
  logic                              ucntr_en;          // pixel counter enable
  acc_t         [16:0]               cntr_recip;        // counter reciprocal table
  logic                              dec_pop;

  //
  // Functions
  //
  // optimized 48b count leading zero bits
  function automatic logic [5:0] clz48(logic [47:0] i);
    logic [5:0]       e;
    logic [15:0]      v;
    logic [15:0][1:0] l;
    logic [7:0][2:0]  m;
    logic [3:0][3:0]  n;
    logic [1:0][4:0]  o;
    v = '0;
    l = '0;
    // loop over only 12
    v[3] = 1'b1;
    for (int c = 0; c < 12; c++)
    begin
      v[c+4]    = i[4*c+:4] != '0;
      l[c+4][0] = (i[4*c+2+:2] == 2'b01) | (i[4*c+1+:3] == 3'b000);
      l[c+4][1] = (i[4*c+2+:2] == 2'b00);
    end
    // binary reduction
    for (int c = 0; c < 8; c++)
    begin
      m[c] = (v[2*c+1] != 1'b0) ? {1'b0,l[2*c+1]} : {1'b1,l[2*c+0]};
    end
    for (int c = 0; c < 4; c++)
    begin
      n[c] = (v[4*c+2+:2] != 2'b00) ? {1'b0,m[2*c+1]} : {1'b1,m[2*c+0]};
    end
    for (int c = 0; c < 2; c++)
    begin
      o[c] = (v[8*c+4+:4] != 4'b0000) ? {1'b0,n[2*c+1]} : {1'b1,n[2*c+0]};
    end
    e = (v[15:8] != 8'b00000000) ? {1'b0,o[1]} : {1'b1,o[0]};
    return e;
  endfunction : clz48


  //
  // simple assignments
  //
  assign wr_typ     = wr_val_r ? wr_typ_r : ot_no;
  assign wr_ad      = wr_ad_r;
  assign wr_val_nxt = (wr_val_r & stall) | (fu_valid & ~stall);
  assign wr_en      = fu_valid & ~stall;
  assign wr_typ_nxt = fu_inst.fmt[0];
  assign wr_ad_nxt  = fu_inst.ops[0];
  assign padval     = (opc_r == dec_popin) || (opc_r == dec_fpopin) || (opc_r == dec_fpopinf);
  assign dec_pop    = (fu_inst.opc.i == dec_fpopin) | (fu_inst.opc.i == dec_fpopinf) | (fu_inst.opc.i == dec_popin);
  assign ostall     = fu_valid && 
                      (
                       // stall if gather not accepted
                       ((fu_inst.opc.i == dec_gather || fu_inst.opc.i == dec_gather2d) && (~gather_acc)) ||
                       // stall output in first cycle of double wide input or if not valid
                       (dec_pop & ((~in_valid) | (attr_dbl & ~tgl_r))));
  assign in_accept  = fu_valid & dec_pop & ((~stall) || (attr_dbl & ~tgl_r));
  assign state_en   = wr_val_r & state_en_r & ~stall;
  assign state_en_nxt = fu_inst.opc.i == dec_fpopinf;
  assign gather_val = fu_valid & (GATHEN == 1) & (fu_inst.opc.i == dec_gather || fu_inst.opc.i == dec_gather2d) & ~stall;

  // reciprocal values for 0 to 16 in fp32
  assign cntr_recip = {32'h3d800000,32'h3d888889,32'h3d924925,32'h3d9d89d9,
                       32'h3daaaaab,32'h3dba2e8c,32'h3dcccccd,32'h3de38e39,
                       32'h3e000000,32'h3e124925,32'h3e2aaaab,32'h3e4ccccd,
                       32'h3e800000,32'h3eaaaaab,32'h3f000000,32'h3f800000,
                       32'h00000000};

  //
  // Create double data from input
  //
  
  // toggle state if double wide input
  assign tgl_nxt = in_valid & in_accept & attr_dbl & dec_pop ? ~tgl_r : tgl_r;
  assign data_en = in_valid & in_accept & attr_dbl & dec_pop & ~tgl_r;
// spyglass disable_block Reset_check07
//SMD:Reset is driven by combinational logic
//SJ :Reset CTRL module TMR CDC is not correctly recognized
  // outputs: tgl_r, data_r
  always_ff @(posedge clk or posedge rst_a)
  begin : tgl_reg_PROC
    if (rst_a == 1'b1)
    begin
      tgl_r  <= 1'b0;
      data_r <= '0;
    end
    else
    begin
      tgl_r  <= tgl_nxt;
      if (data_en)
      begin
        data_r <= in_data;
      end
    end
  end : tgl_reg_PROC
// spyglass enable_block Reset_check07

  // update unpadded pixel counter
  always_ff @(posedge clk or posedge rst_a)
  begin : ucntr_reg_PROC
    if (rst_a == 1'b1)
    begin
      ucntr_r      <= '0;
    end
    else
    begin
      if (ucntr_en)
      begin
        ucntr_r <= ucntr_nxt;
      end
    end
  end : ucntr_reg_PROC

  // double data width depending on mode
  // outputs: dataw
  always_comb
  begin : dbl_PROC
    if (attr_dbl)
    begin
      if (attr_fm)
      begin
        // double wide feature-map
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression '((2 * i) + 1)'
//SJ :Ignore
        for (int i = 0; i < ISIZE/2; i++)
        begin
          dataw[i]         = {{32{ data_r[2*i+1][7]}},  data_r[2*i+1][7:0],  data_r[2*i+0][7:0]};
          dataw[i+ISIZE/2] = {{32{in_data[2*i+1][7]}}, in_data[2*i+1][7:0], in_data[2*i+0][7:0]};
        end
// spyglass enable_block SelfDeterminedExpr-ML
      end
      else
      begin
        // double wide accumulator
        for (int i = 0; i < ISIZE; i++)
        begin
          dataw[i]         = {in_data[i][23:0],  data_r[i][23:0]};
        end
      end
    end
    else
    begin
      // sign extend from 32b to 48b
      for (int i = 0; i < ISIZE; i++)
      begin
        dataw[i]           = {{16{ in_data[i][31]}},  in_data[i]};
      end
    end
  end : dbl_PROC

  //
  // Compute gather product
  //
  always_comb
  begin : gather_prod_PROC
    offset_t s0;
    offset_t s1;
    s0 = '0;
    s1 = '0;
    if (fu_inst.opc.i == dec_gather2d)
    begin
      s0 = rd_vr7v0l[15:0];
      s1 = rd_vr7v0h[15:0];
    end
    else if (fu_inst.opc.i == dec_gather)
    begin
      s0 = rd_vr7i0[15:0];
      s1 = offset_t'(VID);
    end
    if (GATHEN == 1)
    begin
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      gather_prod = (in_offs0 * s0) + (in_offs1 * s1) + gather_base;
// spyglass enable_block W164a
    end
    else
    begin
      gather_prod = '0;
    end
  end : gather_prod_PROC

  //
  // Select floating-point feature-map input
  //
  // output: fp_scale_in
  always_comb
  begin : fpin_sel_PROC
    fp_scale_in = '0;
    case (attr_fmode)
    fmode_int32_e:
      begin
        // int32 -> fp32 load
        // convert integer to floating-point
        for (int i = 0; i < ISIZE; i++)
        begin
          logic        sgn;
          logic [47:0] mantissa;
          logic [7:0]  ex;
          logic [23:0] mantrnd;
          // copy sign bit also on carry input
          sgn  = dataw[i][47];
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
          mantissa = sgn ? ~dataw[i] : dataw[i];
// spyglass enable_block W164a
          mantissa[47] = 1'b0;
          // get exponent by counting sign zero bits
          ex = clz48(mantissa);
          // barrelshift mantissa by exponent, shifting in sign bits
          mantissa = ex[5] ? {mantissa[15:0],{32{sgn}}} : mantissa;
          mantissa = ex[4] ? {mantissa[31:0],{16{sgn}}} : mantissa;
          mantissa = ex[3] ? {mantissa[39:0],{ 8{sgn}}} : mantissa;
          mantissa = ex[2] ? {mantissa[43:0],{ 4{sgn}}} : mantissa;
          mantissa = ex[1] ? {mantissa[45:0],{ 2{sgn}}} : mantissa;
          mantissa = ex[0] ? {mantissa[46:0],{ 1{sgn}}} : mantissa;
          // add sign for negation and 1/2 lsb
          mantissa = {1'b0, mantissa[46:0]} + sgn + 24'h800000;
          // convergent rounding
          mantissa[24] &= mantissa[23:0] != '0;
          // select rounded bits
          mantrnd = mantissa[47:24];
          // add exponent bias
          //ex = 'd174-ex;
          ex = ('d174|mantrnd[23])-ex;
          if (mantrnd[23])
          begin
            // overflow from rounding
            mantrnd = mantrnd >> 1;
            mantrnd[22] = 1'b0;
            //ex = ex + 'd1;
          end
          if (dataw[i][46:0] == '0)
          begin
            if (dataw[i][47])
            begin
              // special case for 48b MININT
              fp_scale_in[i] = 32'hd7000000;
            end
            else
            begin
              fp_scale_in[i] = {dataw[i][47],31'h0};
            end
          end
          else
          begin
            fp_scale_in[i] = {dataw[i][47],ex,mantrnd[22:0]};
          end
        end
      end
    fmode_fp16_e:
      // fp16 -> fp32 load
      begin
        for (int i = 0; i < ISIZE; i++) begin
          fp_scale_in[i][31] = dataw[i][15];
          case (dataw[i][14:10])
          5'h1f:
            begin
              fp_scale_in[i][30:0] = '1;
            end
          5'h00:
            begin
              fp_scale_in[i][30:0] = '0;
            end
          default:
            begin
              fp_scale_in[i][30:23] = {dataw[i][14], ~{3{dataw[i][14]}}, dataw[i][13:10]};
              //fp_scale_in[i][30:23] = {dataw[i][14] ? 4'b1000 : 4'b0111, dataw[i][13:10]};
              //fp_scale_in[i][30:23] = dataw[i][14:10] + 8'd112;
              fp_scale_in[i][22:0]  = {dataw[i][9:0], 13'd0};
            end
          endcase // case (dataw[i][14:10])
        end
      end
    fmode_bf16_e:
      // bf16 -> fp32 load
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          fp_scale_in[i][31]    = dataw[i][15];
          fp_scale_in[i][30:23] = dataw[i][14:7];
          fp_scale_in[i][22:0]  = {dataw[i][6:0], 16'd0};
        end
      end
    default:
      // fp32 -> fp32 load
      begin
        for (int i = 0; i < ISIZE; i++)
        begin
          fp_scale_in[i] = dataw[i][31:0];
        end
      end
    endcase // case (attr_fmode)
  end : fpin_sel_PROC

  
  //
  // Prescale the input
  //
  for (genvar gi = 0; gi < ISIZE; gi++)
  begin : prescale_GEN
    logic [7:0] src1;
    assign src1 = fu_inst.fmt[2] == ot_no ? 8'h7c : rd_data[1][gi][7:0];    
    assign fp_scale_out_nxt[gi] = fu_inst.opc.i == dec_popin ? dataw[gi][31:0] : fp_scale_out_tmp[gi];
    npu_fp_prescale
    u_prescale_inst
      (
       .a ( fp_scale_in[gi]      ),
       .b ( src1                 ),
       .z ( fp_scale_out_tmp[gi] )
       );
  end : prescale_GEN

  
  //
  // Pipeline stage
  //
  // registers
  // outputs: wr_val_r, wr_typ_r, wr_ad_r, fp_scale_out_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : pipe_reg_PROC
    if (rst_a == 1'b1)
    begin
      wr_val_r       <= 1'b0;
      wr_typ_r       <= ot_no;
      wr_ad_r        <= '0;
      opc_r          <= dec_fpopin;
      fmt_r          <= ot_no;
      state_en_r     <= 1'b0;
      fp_scale_out_r <= '0;
    end
    else
    begin
      wr_val_r       <= wr_val_nxt;
      if (wr_en)
      begin
        // write-back controls
        wr_typ_r       <= wr_typ_nxt;
        wr_ad_r        <= wr_ad_nxt;
        opc_r          <= fu_inst.opc.i;
        fmt_r          <= fu_inst.fmt[1];
        state_en_r     <= state_en_nxt;
        // results from partial multiplication
        fp_scale_out_r <= fp_scale_out_nxt;
      end
    end
  end : pipe_reg_PROC
  

  //
  // Apply bias
  //
  for (genvar gj = 0; gj < ISIZE; gj++)
  begin : bias_GEN
    logic [31:0] src0;
    assign src0 = fmt_r == ot_no ? '0 : rd_data[0][gj];
    npu_fp_add
    u_add_inst
      (
       .a (fp_scale_out_r[gj]),
       .b (src0              ),
       .z (fp_bias_out[gj]   )
       );
  end : bias_GEN
    

  //
  // Result
  //
  // output: wr_data, ucntr_nxt
  always_comb
  begin : comp_PROC
    // local variables
    logic [ISIZE/4-1:0][4:0]   ucntr_pre;     // unpadded pixel counter logic
    // default
    ucntr_en  = 1'b0;
    ucntr_pre = it_first ? '0 : ucntr_r; // reset at start of HLAPI
    padacc    = 1'b0;
    ucntr_nxt = '0;
    wr_data   = '0;
    case (opc_r)
    dec_fpopin, dec_fpopinf:
      begin
        // fpopin
        ucntr_en   = wr_val_r & ~stall;
        padacc     = ucntr_en;
        for (int i = 0; i < ISIZE/4; i++)
        begin
          ucntr_nxt[i] = padflag[i] ? ucntr_pre[i] : ucntr_pre[i] + 'd1;
        end
        for (int i = 0; i < ISIZE; i++)
        begin
          wr_data[i] |= fp_bias_out[i];
        end
      end
    dec_popin:
      begin
        // popin
        padacc      = wr_val_r & ~stall;
        wr_data    |= fp_scale_out_r;
      end
    dec_fpoprecip:
      begin
        if (ID == 0)
        begin
          logic [31:0] cval;
          ucntr_en   = ~stall; // clear counter
          for (int i = 0; i < ISIZE/4; i++)
          begin
            cval = cntr_recip >> {ucntr_r[i],5'd0};
            wr_data[4*i+:4] |= {4{cval}};
          end
        end
      end
    dec_poppad:
      begin
        if (ID == 1)
        begin
          for (int i = 0; i < ISIZE/4; i++)
          begin
            for (int j = 0; j < 4; j++)
            begin
              wr_data[4*i+j][0] |= padflag[i];
            end
          end
        end
      end
    default:
      begin
        // popidx, return MININT if padded
        if (ID == 1)
        begin
          for (int i = 0; i < ISIZE/4; i++)
          begin
            for (int j = 0; j < 4; j++)
            begin
              wr_data[4*i+j] |= padflag[i] ? 32'h80000000 : {{16{cidx[i][15]}}, cidx[i]};
            end
          end
        end
      end
    endcase
    // output state not used
    state = '0;
  end : comp_PROC

endmodule : npu_gtoa_fu_in
