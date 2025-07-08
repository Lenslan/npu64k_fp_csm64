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
// NPU convolution multiplier array
//

// vcs -sverilog ../../../build/verilog/RTL/npu_types.sv npu_conv_types.sv npu_conv_mpy_prim10.sv npu_conv_mpy_prim8.sv npu_conv_mpy_mul.sv +incdir+../../../build/verilog/RTL +libext+.v -y $SYNOPSYS/dw/sim_ver

module npu_conv_mpy_mul
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT=1)
  (
   input  logic                              clk,      // Clock, all logic clocked at posedge
   input  logic                              rst_a,    // Asynchronous reset, active high
   input  logic                              mpy_en,   // multiplier output register enable
   input  mpy_fm_t    [ISIZE-1:0][ISIZE-1:0] mpy_a,    // feature-maps
   input  mpy_cf_t    [ISIZE-1:0][ISIZE-1:0] mpy_b,    // coefficients
   output out_prods_t [ISIZE-1:0]            prods,    // output products
   input  mpy_cfg_t                          mpycfg    // configuration
   );
  // local wires
  out_prods_t [ISIZE-1:0]                 prod_nxt; // next state of products
  out_prods_t [ISIZE-1:0]                 prod_r;   // registered products
  logic                                   fp;       // floating-point mode else integer

  //
  // simple assignments
  //
  assign fp    = isfp(mpycfg);
  assign prods = prod_r;
  
  //
  // sign, pairs of multipliers and exponent
  //
  for (genvar go = 0; go < ISIZE; go++) 
  begin : o_GEN
    logic [ISIZE-1:0][7:0] esum;     // sum of exponents
    logic [ISIZE-1:0]      ezero;    // exp will be zero
    logic [ISIZE-1:0]      nan;      // product is nan
    logic [7:0]            me;
    for (genvar gi = 0; gi < ISIZE; gi++) 
    begin : i_GEN
      logic   [16:0] prodb;
      prodb_t        pb;
      
      // multiply even feature-map inputs: int8 or lsb of int16 feature-map or float mantissa
      logic [9:0]  tsum;
      if (NPU_HAS_FLOAT)
      begin : mpy12
        logic upper_a;
        logic upper_b;
        assign upper_a = fp ? 1'b1 : mpy_a[go][gi].sgn;      
        assign upper_b = fp ? 1'b1 : mpy_b[go][gi].sgn;      
        // DW02_mult 
        //   #(
        //     .A_width(11),
        //     .B_width(11)
        //     )
        // u_mpy12_inst
        //   (
        //    .A({upper_a,mpy_a[go][gi].int10[9:0]}),
        //    .B({upper_b,mpy_b[go][gi].int10[9:0]}),
        //    .TC(!fp),
        //    .PRODUCT(prod_nxt[go].proda[gi])
        //    );
	assign prod_nxt[go].proda[gi] = fp ? {{upper_a,mpy_a[go][gi].int10[9:0]}} * {{upper_b,mpy_b[go][gi].int10[9:0]}} :
                           		     $signed({{upper_a,mpy_a[go][gi].int10[9:0]}}) * $signed({{upper_b,mpy_b[go][gi].int10[9:0]}}) ;
      end // if (NPU_HAS_FLOAT)
      else
      begin : mpy12_el
        // 9b x 9b multiplier, because of sign extension
        // needed for fm16 mode!
        assign prod_nxt[go].proda[gi][21:18] = '0;
        // DW02_mult #(.A_width(9),.B_width(9))
        // u_mpy9a_inst
        //   (
        //    .A(mpy_a[go][gi].int10[8:0]),
        //    .B(mpy_b[go][gi].int10[8:0]),
        //    .TC(1'b1),
        //    .PRODUCT(prod_nxt[go].proda[gi][17:0])
        //    );
	assign prod_nxt[go].proda[gi][17:0] = $signed(mpy_a[go][gi].int10[8:0]) * $signed(mpy_b[go][gi].int10[8:0]);
      end
      
      // DW02_mult 
      // #(
      //   .A_width(8),
      //   .B_width(9)
      // )
      // u_mpy_9_inst
      // (
      //  .A(mpy_a[go][gi].int8),
      //  .B(mpy_b[go][gi].int9),
      //  .TC(1'b1),
      //  .PRODUCT(prodb)
      // );
	assign prodb = $signed(mpy_a[go][gi].int8) * $signed(mpy_b[go][gi].int9);
 
      // process floating-point exponent
      always_comb
      begin : exp_PROC
        if (NPU_HAS_FLOAT)
        begin
          // add the two exponents... valid outputs: from 0 to 255
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
          tsum      = {2'b00,mpy_a[go][gi].int8} + {mpy_b[go][gi].int9[8], mpy_b[go][gi].int9[8:0]};
// spyglass enable_block W164a
          // it's zero if the incoming values were zero, or if the sum underflowed but take care of 0*nan=nan
          ezero[gi] = (tsum[9] | tsum==0 | mpy_a[go][gi].zero | mpy_b[go][gi].zero);
          // it's nan if the incoming values were nan, or if the sum overflowed
          nan[gi]   = (tsum[9:8]==2'b01) | mpy_a[go][gi].nan  | mpy_b[go][gi].nan;
          // force zero mantissa
          esum[gi]  = ezero[gi] ? '0 : tsum[7:0];
        end // if (NPU_HAS_FLOAT)
        else
        begin
          ezero[gi] = '0;
          nan[gi]   = '0;
          esum[gi]  = '0;
        end
      end // block: exp_PROC
  
          
      // select register inputs: product b output in int mode; sign/zero/delta in fp mode
      always_comb
      begin : prodb_PROC
        pb.i         = prodb;
        if (NPU_HAS_FLOAT && fp)
        begin
          pb.f.sgn   = mpy_a[go][gi].sgn ^ mpy_b[go][gi].sgn;
          pb.f.zero  = ezero[gi];
          pb.f.e     = tsum[7:0];
        end
      end : prodb_PROC
      assign prod_nxt[go].prodb[gi] = pb;
      
    end : i_GEN

    // reduce nan
    assign prod_nxt[go].nan = |nan;
 
    //
    // Maximum exponent
    //
    // outputs: prod_nxt[go].maxexp
    assign prod_nxt[go].maxexp = me;
    always_comb
    begin : max_PROC
      logic [3:0][7:0] m;
      logic [3:0][3:0] f;
      // default outputs
      me = '0;
      m  = '0;
      if (NPU_HAS_FLOAT)
      begin
        // reduce to 4*8b
        for (int g = 0; g < 4; g++)
        begin
          // find maximum of 4
          f = '0;
          for (int i = 0; i < 4; i++)
          begin
            f[i][i] = 1'b1;
            for (int j = 0; j < i; j++)
            begin
              f[i][j] = esum[g*4+i] >= esum[g*4+j];
              f[j][i] = ~f[i][j];
            end
          end
          for (int i = 0; i < 4; i++)
          begin
            m[g] |= (&f[i]) ? esum[g*4+i] : '0;
          end
        end
        // reduce to 1*8b
        f = '0;
        for (int i = 0; i < 4; i++)
        begin
          f[i][i] = 1'b1;
          for (int j = 0; j < i; j++)
          begin
            f[i][j] = m[i] >= m[j];
            f[j][i] = ~f[i][j];
          end
        end
        for (int i = 0; i < 4; i++)
        begin
          me |= (&f[i]) ? m[i] : '0;
        end
      end
    end : max_PROC
    
  end : o_GEN
  
  //
  // Output registers
  //
  always_ff @(posedge clk or posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      prod_r <= '0;
    end
    else if (mpy_en)
    begin
      prod_r <= prod_nxt;
    end
  end : state_PROC

endmodule : npu_conv_mpy_mul
