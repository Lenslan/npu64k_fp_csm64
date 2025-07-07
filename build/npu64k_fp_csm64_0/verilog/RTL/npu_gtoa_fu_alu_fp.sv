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

// GTOA floating-point ALU, operations:
// - floatig-point add/subtract:                            FADD
// - floating-point truncate to integer value towards zero: TRUNC
// - floating-point fractional part of integer towards 0:   FRAC
// - renormalize floating-point:                            RENORM
// - floating-point to integer:                             FTOI
// - integer to floating-point:                             ITOF
// future extension:
// - integer:                                               ADD/SUB/RSUB
// - integer shift left:                                    SL
// - integer arithmetic shift right:                        ASR
// - integer logic shift right:                             LSR

module npu_gtoa_fu_alu_fp
  import npu_gtoa_types::*;
  (
   input  fp_oh_idx_t        opc_oh, // operation, one-hot zero
   input  logic       [31:0] a,      // a operand
   input  logic       [31:0] b,      // b operand
   output logic       [31:0] z       // result
   );
  // local wires
  logic [31:0] lrge;                 // input operand with largest magnitude
  logic [31:0] smll;                 // input operand with smallest magnitude
  logic [7:0]  e_lrge,e_smll;        // exponents
  logic [27:0] m_lrge,m_smll;        // the mantissa numbers
  logic [31:0] m_norm;               // small mantissa normalized
  logic        ov_norm;              // overflow from normalization
  logic [31:0] m_z;                  // the mantissa numbers
  logic        ov_z;                 // adder overflow
  logic [4:0]  nrm;                  // leading zero count
  logic [31:0] m_s;                  // the normalized mantissa
  logic [8:0]  e_rnd;                // exponent after rounding
  logic [22:0] m_o;                  // the rounded mantissa
  logic        nov;                  // no overflow after rounding
  logic [8:0]  norm_shamt;           // renorm shift amount


  ////////////////////////////////////////////////////////
  //
  // Functions
  //
  ////////////////////////////////////////////////////////
  
  //
  // sticky shift right ORing all dropped bits into lsb
  //
  function automatic logic [31:0] stickyshift(logic [31:0] i, logic [4:0] shamt);
    logic [31:0] res;
    res = i;
    if (shamt[0])
    begin
      res[1] = |res[1:0];
      res = {1'd0,res[31:1]};
    end
    if (shamt[1])
    begin
      res[2] = |res[2:0];
      res = {2'd0,res[31:2]};
    end
    if (shamt[2])
    begin
      res[4] = |res[4:0];
      res = {4'd0,res[31:4]};
    end
    if (shamt[3])
    begin
      res[8] = |res[8:0];
      res = {8'd0,res[31:8]};
    end
    if (shamt[4])
    begin
      res[16] = |res[16:0];
      res = {16'd0,res[31:16]};
    end
    return res;
  endfunction : stickyshift


  //  
  // barrelshift left
  //
  function automatic logic [31:0] barrelshift(logic [31:0] i, logic [4:0] shamt);
    logic [31:0] res;
    res = i;
    if (shamt[4])
    begin
      res = {res[15:0],16'd0};
    end
    if (shamt[3])
    begin
      res = {res[23:0],8'd0};
    end
    if (shamt[2])
    begin
      res = {res[27:0],4'd0};
    end
    if (shamt[1])
    begin
      res = {res[29:0],2'd0};
    end
    if (shamt[0])
    begin
      res = {res[30:0],1'd0};
    end
    return res;
  endfunction : barrelshift
  
  
  //
  // optimized 32b count leading zero bits
  //
  function automatic logic [4:0] clz32(logic [31:0] i);
    logic [4:0]      e;
    logic [7:0]      v;
    logic [7:0][1:0] l;
    logic [3:0][2:0] m;
    logic [1:0][3:0] n;
    v = '0;
    l = '0;
    // loop over 8 groups of 4b
    for (int c = 0; c < 8; c++)
    begin
      v[c]    = i[4*c+:4] != '0;
      l[c][0] = (i[4*c+2+:2] == 2'b01) | (i[4*c+1+:3] == 3'b000);
      l[c][1] = (i[4*c+2+:2] == 2'b00);
    end
    // binary reduction
    for (int c = 0; c < 4; c++)
    begin
      m[c] = (v[2*c+1] != 1'b0) ? {1'b0,l[2*c+1]} : {1'b1,l[2*c+0]};
    end
    for (int c = 0; c < 2; c++)
    begin
      n[c] = (v[4*c+2+:2] != 2'b00) ? {1'b0,m[2*c+1]} : {1'b1,m[2*c+0]};
    end
    e = (v[7:4] != 4'b0000) ? {1'b0,n[1]} : {1'b1,n[0]};
    return e;
  endfunction : clz32
  

  ////////////////////////////////////////////////////////
  //
  // Always blocks
  //
  ////////////////////////////////////////////////////////
  
  //
  // Find biggest and smallest magnitude operands for adder
  //
  // outputs: lrge, e_lrge, e_smll, f_lrge, f_smll
  always_comb
  begin : swap_PROC
    logic        e_swap;
    logic        f_swap;
    logic [22:0] f_lrge,f_smll;        // fractions
    logic        s_lrge,s_smll;        // signs
    e_swap   = a[30:23] < b[30:23];
    f_swap   = a[30:0]  < b[30:0];

    e_lrge   = e_swap ? b[30:23] : a[30:23];
    e_smll   = e_swap ? a[30:23] : b[30:23];
    f_lrge   = f_swap ? b[22:0] : a[22:0];
    f_smll   = f_swap ? a[22:0] : b[22:0];
    s_lrge   = f_swap ? b[31] : a[31];
    s_smll   = f_swap ? a[31] : b[31];
    
    lrge     = {s_lrge,e_lrge,f_lrge};
    smll     = {s_smll,e_smll,f_smll};

    // mantissas with leading 1
    m_lrge = {2'b01,f_lrge,3'b000};
    m_smll = {2'b01,f_smll,3'b000};
  end : swap_PROC

  
  //
  // Denormalize the small input to exponent of large input
  // use a sticky shifter that ORs all bits shifted out into lsb
  //
  // outputs: m_norm, ov_norm, norm_shamt
  always_comb
  begin : norm_in_PROC
    logic [7:0]  e_a;       // exponent a
    logic [7:0]  e_b;       // exponent b
    logic [7:0]  e_c;       // exponent offset
    logic [31:0] shin;      // shifter input
    // default values
    shin       = '0;
    e_a        = '0;
    e_b        = '0;
    e_c        = '0;
    m_norm     = '0;
    ov_norm    = 1'b0;
    norm_shamt = '0;
    // select inputs, depending on opcode
    if (opc_oh[fp_add_oh_idx])
    begin
      // floating-point add, denormalize small input
      e_a    |= e_lrge;
      e_b    |= e_smll;
      shin   |= {4'd0,m_smll};
    end
    if (opc_oh[fp_ftoi_oh_idx])
    begin
      // floating-point to integer
      e_a    |= 'd157; // 127+30
      e_b    |= a[30:23];
      shin   |= {1'b1,a[22:0],8'd0};
    end
    if (opc_oh[fp_trunc_oh_idx])
    begin
      // trunc, shift mask by a-127
      e_a    |= a[30:23];
      e_b    |= 'd127;
      shin   |= {31'h007fffff,1'b0};
    end
    if (opc_oh[fp_fract_oh_idx])
    begin
      // fract, shift mask by a-127
      e_a    |= a[30:23];
      e_b    |= 'd127;
      shin   |= {31'h007fffff,1'b0};
    end
    if (opc_oh[fp_renorm_oh_idx])
    begin
      // renorm, shift mask by a-b+24
      e_a    |= a[30:23];
      e_b    |= b[7:0];
      e_c    |= 'd24;
      shin   |= {31'h00ffffff,1'b0};
    end
    // compute shift amount: a-b+c=a+~b+c+1
    e_c[0] = 1'b1;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    {ov_norm,norm_shamt} = {2'b00,e_a} + {2'b11,~e_b} + {2'b00,e_c};
// spyglass enable_block W164a
    // select output
    if (norm_shamt[8:5] == '0)
    begin
      // no shift underflow, do sticky shift right
      m_norm |= stickyshift(shin, norm_shamt[4:0]);
    end
  end : norm_in_PROC
  

  //
  // Adder/subtracter
  //
  // outputs: m_z, ov_z
  always_comb
  begin : addsub_PROC
    logic [31:0] add_a;   // a operand
    logic [31:0] add_b;   // b operand
    logic        add_cin; // c operand
    // defaults
    add_a   = '0;
    add_b   = '0;
    // select adder inputs
    if (opc_oh[fp_add_oh_idx])
    begin
      // floating-point add
      add_a[31:4] |= m_lrge;
      add_b[31:4] |= m_norm[27:0];
    end
    if (opc_oh[fp_fract_oh_idx])
    begin
      // fract mask
      add_a       |= {1'b0,a[22:0]&m_norm[23:1],8'd0};
    end
    if (opc_oh[fp_itof_oh_idx])
    begin
      // itof absolute value
      add_b       |= a;
    end
    add_cin = a[31] ^ b[31];
    add_b   = add_b ^ {32{add_cin}};
    // actual adder
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    {ov_z,m_z} = {add_a[31],add_a} + {add_b[31],add_b} + add_cin;
// spyglass enable_block W164a
  end : addsub_PROC
  

  //
  // Normalize so 1 at position 31
  //
  // outputs: nrm
  always_comb
  begin : add_norm_PROC
    logic [31:0] clzin;
    // default
    clzin = '0;
    // prepare for normalization, counting leading 0
    if (opc_oh[fp_add_oh_idx])
    begin
      // FP add
      clzin |= {m_z[31:4], 4'b1000};
    end
    if (opc_oh[fp_itof_oh_idx])
    begin
      // itof
      clzin |= m_z;
    end
    if (opc_oh[fp_fract_oh_idx])
    begin
      // fract
      clzin |= {1'b0,m_z[30:8],8'h0};
    end
    nrm = clz32(clzin);
    // barrel shift left
    m_s = barrelshift(m_z, nrm);
  end : add_norm_PROC
  

  //
  // Rounding
  //
  // outputs e_rnd, nov, m_o
  always_comb
  begin : rnd_PROC
    logic [32:0] add_a;
    logic [32:0] add_b;
    logic [32:0] add_c;
    logic [24:0] lsb_clr; // clear lsb after adding
    // default
    add_a   = '0;
    add_b   = '0;
    add_c   = '0;
    lsb_clr = '0;
    // instruction dependent
    if (opc_oh[fp_add_oh_idx])
    begin
      // floating-point add
      add_a      |= {1'b0,e_lrge,1'b1,m_s[30:8]};
      add_b      |= {9'h2,24'h0};
      add_c      |= {4'b1111,~nrm,23'h0, m_s[7]};
      lsb_clr[0] |= (~m_s[8])&(m_s[6:4]==3'b000);
    end
    if (opc_oh[fp_ftoi_oh_idx])
    begin
      // floating-point to integer, negate
      add_a      |= {a[31], {1'b0,m_norm[31:1]}^{32{a[31]}}};
      add_c[0]   |= a[31];
    end
    if (opc_oh[fp_itof_oh_idx])
    begin
      // integer to floating-point normalization
      add_a      |= {1'd0,8'd159,1'b1,m_s[30:8]};
      add_c      |= {4'b1111,~nrm,23'h0, m_s[7]};
      lsb_clr[0] |= (~m_s[8])&(m_s[6:0]==7'd0);
    end
    if (opc_oh[fp_fract_oh_idx])
    begin
      // fract: subtract nrm from input exponent
      add_a      |= {1'd0,a[30:23],1'b1,m_s[30:8]};
      add_b      |= {1'd0,~{3'd0,nrm},24'd0};
      add_c      |= {8'd0,1'b1,24'd0};
    end
    if (opc_oh[fp_renorm_oh_idx])
    begin
      // renorm masking
      logic [23:0] maskp5; // bit set at 1/2lsb
      logic        lsb;
      logic        stky;
      // renorm mask and round ties to nearest even
      maskp5      = m_norm[24:1]&~m_norm[25:2];
      lsb         = |({1'b1,a[22:0]}&{maskp5[22:0],1'b0});
      stky        = |(a[22:0]&m_norm[24:2]);
      add_a      |= {1'b0,a[30:23],{1'b1,a[22:0]}&~m_norm[24:1]};
      add_b      |= {8'd0,{1'b1,a[22:0]}&maskp5,1'b0};
      lsb_clr    |= (~(lsb|stky)) ? {maskp5,1'b0}  : '0;
    end
    // round ties to nearest even, overflow into exponent
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    {e_rnd,nov,m_o} = add_a + add_b + add_c;
// spyglass enable_block W164a
    {e_rnd[0],nov,m_o} = {e_rnd[0],nov,m_o} & (~lsb_clr);
  end : rnd_PROC
  
  
  //
  // Output selection
  //
  // outputs: z
  always_comb
  begin : out_PROC
    z = '0;
    if (opc_oh[fp_add_oh_idx])
    begin
      // floating-point add
      if (e_smll == 8'hff)
      begin
        // both are nan, second operand has higher priority
        z |= {b[31], {31{1'b1}}};
      end
      else if (e_lrge == 8'hff)
      begin
        // biggest is nan or inf
        z |= {lrge[31], {31{1'b1}}};
      end
      else if (e_lrge == 8'h00)
      begin
        // both are 0: 0 + -0 = 0; -0 + 0 = 0; -0 + -0 = -0;
        z |= {lrge[31] & smll[31], {31{1'b0}}};
      end
      else if (e_smll == 8'h00)
      begin
        // smallest is 0
        z |= lrge;
      end
      else if (m_z[31:4] == '0)
      begin
        // exact zero, return +0
        z |= '0;
      end
      else if (e_rnd[8] || (e_rnd[7:0] == '0))
      begin
        // smaller than can be represented --> zero
        z |= {lrge[31], {31{1'b0}}};
      end
      else if (&e_rnd[7:0])
      begin
        // nan
        z |= {lrge[31],31'h7fffffff};
      end
      else if (nov)
      begin
        // no rounding overflow
        z |= {lrge[31],e_rnd[7:0],m_o};
      end
      else
      begin
        // overflow from rounding
        z |= {lrge[31],e_rnd[7:0],1'b0,m_o[22:1]};
      end
    end
    if (opc_oh[fp_ftoi_oh_idx])
    begin
      // floating-point to integer
      if (a[30:23] >= 'd158)
      begin
        // overflow, set to max/minint
        z |= {a[31],{31{~a[31]}}};
      end
      else 
      begin
        // normal
        z |= {e_rnd[7:0],nov,m_o};
      end
    end
    if (opc_oh[fp_itof_oh_idx])
    begin
      // integer to floating-point
      if (a == '0)
      begin
        z |= '0;
      end
      else if (nov)
      begin
        // no rounding overflow
        z |= {a[31],e_rnd[7:0],m_o};
      end
      else
      begin
        // overflow from rounding
        z |= {a[31],e_rnd[7:0],1'b0,m_o[22:1]};
      end
    end
    if (opc_oh[fp_trunc_oh_idx])
    begin
      // trunc
      if (a[30:23] == 8'hff)
      begin
        // nan
        z |= {a[31],{31{1'b1}}};
      end
      else if (a[30:23] < 'd127)
      begin
        // no integer bits
        z |= {a[31],{31{1'b0}}};
      end
      else
      begin
        // mask mantissa bits
        z |= {a[31:23],a[22:0]&~m_norm[23:1]};
      end
    end
    if (opc_oh[fp_fract_oh_idx])
    begin
      // fract
      if (a[30:23] == 8'hff)
      begin
        // nan
        z |= {a[31],{31{1'b1}}};
      end
      else if (a[30:23] < 'd127)
      begin
        z |= a;
      end
      else if (a[30:23] >= 'd150 || a[30:23] == '0 || (!m_s[31]))
      begin
        // fraction is 0, keep sign
        z |= {a[31],31'd0};
      end
      else
      begin
        // normalized
        z |= {a[31],e_rnd[7:0],m_o[22:0]};
      end
    end
    if (opc_oh[fp_renorm_oh_idx])
    begin
      // renorm
      if (a[30:23] == 8'hff || b[7:0] == 8'hff)
      begin
        // nan
        z |= {a[31],{31{1'b1}}};
      end
      else if (ov_norm || a[30:23] == '0 || norm_shamt == '0)
      begin
        // overflow from normalization
        z |= {a[31],{31{1'b0}}};
      end
      else if (!nov)
      begin
        // overflow from rounding
        z |= {a[31],e_rnd[7:0],1'b0,m_o[22:1]};
      end
      else
      begin
        // no rounding overflow
        z |= {a[31],e_rnd[7:0],m_o};
      end
    end
  end : out_PROC

endmodule : npu_gtoa_fu_alu_fp
