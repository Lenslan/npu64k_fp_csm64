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
 * This module implements the GTOA register file
 */
`include "npu_defines.v"


module npu_gtoa_rf
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int NRD =   1+ 2+ 1+ 2+ 2+ 2+ 2,    // number of read ports
    parameter int NWR =      1+ 1+ 1+    1+ 1,    // number of write ports
    parameter int VRD = 'b0_11__1_11_01_00_00,    // vector read port enable
    parameter int SRD = 'b1_00__0_01_00_00_00,    // scalar read port enable
    parameter int WRD = 'b0_10__1_10_00_01_01,    // parameter word read port enable
    parameter int HRD = 'b0_10__0_10_10_00_00,    // parameter half-word read port enable
    parameter int BRD = 'b0_00__0_10_10_10_10,    // parameter byte read port enable
    parameter int SWR =    'b0__0__1_____0__0     // scalar write port enable
    )
  (
   input  logic                                    clk,           // clock
   input  logic                                    rst_a,         // asynchronous reset, active high
   // update from HLAPI struct
   input  logic                                    hlp_valid,     // HLAPI valid
   input  act_scalar_t [ACT_SREG_INI-1:0]          hlp_scalin,    // scalar array from HLAPI
   // result to HLAPI struct
   output act_scalar_t                             hlp_scalout,   // scalar to HLAPI
   // parameter updates
   input  logic                                    bpar_we,       // write next block of per channel parameters
   input  ixacc_t      [ACT_BREG_NUM-1:0]          bpar_nxt,      // per channel parameters
   // read ports, combinatorial
   input  logic        [NRD-1:0]                   rd_ren,        // if true then valid instruction
   input  act_op_sel_t [NRD-1:0]                   rd_vad,        // vector read operand select
   input  logic        [NRD-1:0][ACT_SREG_NUM-1:0] rd_sad_oh,     // scalar read operand address
   input  logic        [NRD-1:0]                   rd_b_oh,       // if true then parameter read
   input  logic        [NRD-1:0][ISIZE-1:0]        rd_b_hi,       // if true then read upper half parameter
   input  logic        [NRD-1:0][ACT_BREG_NUM-1:0] rd_wad_oh,     // word parameter read operand address
   input  logic        [NRD-1:0][ACT_BREG_NUM-1:0] rd_had_oh,     // half-word parameter read operand address
   input  logic        [NRD-1:0][ACT_BREG_NUM-1:0] rd_bad_oh,     // byte parameter read operand address
   output vyixacc_t    [NRD-1:0]                   rd_data,       // read data
   output acc_t        [VSIZE-1:0]                 rd_vr7i0,      // fixed wire for vr7 i0 data read
   output acc_t        [ISIZE-1:0]                 rd_vr7v0,      // fixed wire for vr7 v0 data read
   // write ports
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   input  act_ot_t     [VSIZE-1:0][NWR-1:0]        wr_typ,        // write operand type
// spyglass enable_block W240
   input  logic        [VSIZE-1:0][NWR-1:0][2:0]   wr_ad,         // write operand address
   input  vyixacc_t               [NWR-1:0]        wr_data,       // write data
   // transpose instruction
   input  logic        [VSIZE-1:0]                 rf_trnsp,      /// transpose VR0,VR1 (NPU4K), VR0..VR7 (NPU1K)
   // flow control
   input  logic                                    stall          // pipeline stall
   );
  // local wires
  logic         [ACT_SREG_NUM-1:0]            hlp_scalar_en;     // HLAPI init scalar register enable
  act_scalar_t  [ACT_SREG_NUM-1:0]            hlp_scalar_nxt;    // HLAPI init scalar registers,  next state
  logic         [VSIZE-1:0][ACT_VREG_NUM-1:0] trnsp_vector_en;   // Transpose vector register enable
  vyixacc_t     [ACT_VREG_NUM-1:0]            trnsp_vector_nxt;  // Transpose vector registers,  next state
  logic         [ACT_SREG_NUM-1:0]            alu0_scalar_en;    // ALU0 scalar register enable
  logic         [VSIZE-1:0][ACT_VREG_NUM-1:0] alu0_vector_en;    // ALU0 vector register enable
  act_scalar_t  [ACT_SREG_NUM-1:0]            alu0_scalar_nxt;   // ALU0 scalar registers,  next state
  vyixacc_t     [ACT_VREG_NUM-1:0]            alu0_vector_nxt;   // ALU0 vector registers,  next state
  logic         [ACT_SREG_NUM-1:0]            other_scalar_en;   // Other FU scalar register enable
  logic         [VSIZE-1:0][ACT_VREG_NUM-1:0] other_vector_en;   // Other FU vector register enable
  act_scalar_t  [ACT_SREG_NUM-1:0]            other_scalar_nxt;  // Other FU scalar registers,  next state
  vyixacc_t     [ACT_VREG_NUM-1:0]            other_vector_nxt;  // Other FU vector registers,  next state
  logic         [ACT_SREG_NUM-1:0]            scalar_en;         // scalar register enable
  logic         [VSIZE-1:0][ACT_VREG_NUM-1:0] vector_en;         // scalar register enable
  act_scalar_t  [ACT_SREG_NUM-1:0]            scalar_nxt;        // scalar registers,  next state
  vyixacc_t     [ACT_VREG_NUM-1:0]            vector_nxt;        // vector registers,  next state
  vyixacc_t     [ACT_VREG_NUM-1:0]            vector_r;          // vector registers
  act_scalar_t  [ACT_SREG_NUM-1:0]            scalar_r;          // scalar registers
  ixacc_t       [ACT_BREG_NUM-1:0]            bpar_r;            // per channel parameters, ping-pong
  logic                                       bpar_en;           // per channel parameter enable
  logic         [NRD-1:0]                     rd_ill;            // illegal read for TB only
  logic         [NWR-1:0]                     wr_ill;            // illegal write for TB only

  
  // simple assignments
  assign hlp_scalout = scalar_r[0];
  assign bpar_en     = bpar_we & ~stall;
  always_comb
  begin : rd_ill_PROC
    logic [NRD-1:0] wo;
    logic [NRD-1:0] ho;
    logic [NRD-1:0] bo;
    logic [NRD-1:0] so;
    logic [NRD-1:0] vo;
    wo = '0;
    ho = '0;
    bo = '0;
    so = '0;
    vo = '0;
    rd_ill = '0;
    for (int i = 0; i < NRD; i++)
      if (rd_ren[i])
      begin
        wo[i] = rd_wad_oh[i] != '0;
        ho[i] = rd_had_oh[i] != '0;
        bo[i] = rd_bad_oh[i] != '0;
        so[i] = rd_sad_oh[i] != '0;
        vo[i] = vr_check(rd_vad[i]);
        rd_ill[i] |= |({(ACT_BREG_NUM/2){rd_b_hi[i][0]}} & (rd_wad_oh[i][ACT_BREG_NUM/2 +: ACT_BREG_NUM/2] |
                                                            rd_had_oh[i][ACT_BREG_NUM/2 +: ACT_BREG_NUM/2] |
                                                            rd_bad_oh[i][ACT_BREG_NUM/2 +: ACT_BREG_NUM/2]));
      end
    rd_ill |= ((wo & ~WRD) | (ho & ~HRD) | (bo & ~BRD) | (so & ~SRD) | (vo & ~VRD));
  end : rd_ill_PROC


  // reading
  // outputs: rd_data, rd_vr7i0
  always_comb
  begin : rd_PROC
    logic        [ACT_BREG_NUM-1:0][ISIZE-1:0][31:0] wpar;        // per channel word parameters, ping-pong
    logic        [ACT_BREG_NUM-1:0][ISIZE-1:0][15:0] hpar;        // per channel half-word parameters, ping-pong
    logic        [ACT_BREG_NUM-1:0][ISIZE-1:0][7:0]  bpar;        // per channel byte parameters, ping-pong
    // defaults
    rd_data = '0;
    for (int p = 0; p < NRD; p++)
    begin
      wpar = bpar_r;
      for (int i = 0; i < ISIZE; i++)
      begin
        if (rd_b_hi[p][i])
        begin
          // upper registers only
          for (int b = 0; b < ACT_BREG_NUM/2; b++)
          begin
            wpar[b][i] = bpar_r[ACT_BREG_NUM/2+b][i];
          end
        end
      end
      hpar = wpar[0 +: ACT_BREG_NUM/2];
      bpar = wpar[0 +: ACT_BREG_NUM/4];
      if ((WRD&(1<<p)) != 0)
      begin
        // read W parameter operand
        for (int w = 0; w < ACT_BREG_NUM; w++)
        begin
          if (rd_wad_oh[p][w])
          begin
            for (int i = 0; i < ISIZE; i++)
            begin
              rd_data[p][0][i] |= wpar[w][i];
            end       
          end
        end
      end
      if ((HRD&(1<<p)) != 0)
      begin
        // read H parameter operand
        for (int h = 0; h < ACT_BREG_NUM; h++)
        begin
          if (rd_had_oh[p][h])
          begin
            for (int i = 0; i < ISIZE; i++)
            begin
              rd_data[p][0][i] |= {{16{hpar[h][i][15]}}, hpar[h][i]};
            end
          end
        end
      end
      if ((BRD&(1<<p)) != 0)
      begin
        // read B parameter operand
        for (int b = 0; b < ACT_BREG_NUM; b++)
        begin
          if (rd_bad_oh[p][b])
          begin
            for (int i = 0; i < ISIZE; i++)
            begin
              rd_data[p][0][i] |= {{24{bpar[b][i][7]}}, bpar[b][i]};
            end
          end
        end
      end
      if ((SRD&(1<<p)) != 0)
      begin
        // read scalar register operand and broadcast over C
        for (int s = 0; s < ACT_SREG_NUM; s++)
        begin
          rd_data[p][0] |= rd_sad_oh[p][s] ? {ISIZE{scalar_r[s]}} : '0;
        end
      end
      // replicate per-channel and scalars over V
      for (int v = 1; v < VSIZE; v++)
      begin
        rd_data[p][v] |= rd_data[p][0];
      end
      if ((VRD&(1<<p)) != 0)
      begin
        // read vector register operand
        rd_data[p] |= vr_read(rd_vad[p], vector_r);
      end
    end // for (int p = 0; p < NRD; p++)
    // read vr7 i0 data
    for (int v = 0; v < VSIZE; v++)
    begin
      rd_vr7i0[v] = vector_r[7][v][0];
    end
    // read vr7 v0 data
    for (int i = 0; i < ISIZE; i++)
    begin
      rd_vr7v0[i] = vector_r[7][0][i];
    end
  end : rd_PROC


  //
  // Register file write logic, split into four parts: HLAPI initialization of scalar, transpose, FU ALU0, other FU
  //
  
  // HLAPI init
  always_comb
  begin : hlp_scalar_wr_PROC
    // default
    hlp_scalar_en   = '0;
    hlp_scalar_nxt  = '0;
    if (hlp_valid)
    begin
      // initialize scalar array from HLAPI
      for (int r = 0; r < ACT_SREG_INI; r++)
      begin
        hlp_scalar_en[r]  |= 1'b1;
        hlp_scalar_nxt[r] |= hlp_scalin[r];
      end
      // initialize upper scalar registers with 0, 1, 1.0f
      hlp_scalar_en[ACT_SREG_INI]    |= 1'b1;
      hlp_scalar_en[ACT_SREG_INI+1]  |= 1'b1;
      hlp_scalar_nxt[ACT_SREG_INI+1] |= 32'd1;      
      hlp_scalar_en[ACT_SREG_INI+2]  |= 1'b1;
      hlp_scalar_nxt[ACT_SREG_INI+2] |= 32'h3f800000;
      // last scalar register can be used to pass to next hlapi
    end
  end : hlp_scalar_wr_PROC
  
  // transpose function
  always_comb
  begin : transp_wr_PROC
    // default
    trnsp_vector_en  = '0;
    trnsp_vector_nxt = '0;
    // transpose
    for (int j = 0; j < ISIZE/VSIZE; j++)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        trnsp_vector_en[v][j] |= rf_trnsp[v] & (~stall);
        if (rf_trnsp[v])
        begin
          for (int i = 0; i < VSIZE; i++)
          begin
            for (int k = 0; k < ISIZE/VSIZE; k++)
            begin
              trnsp_vector_nxt[k][v][i+j*VSIZE] |= vector_r[j][i][v+k*VSIZE];
            end
          end
        end
      end
    end
  end : transp_wr_PROC
  
  localparam int ALU0_WR_BASE = 2;
  // ALU0 write
  always_comb
  begin : alu0_wr_PROC
    // default
    alu0_scalar_en  = '0;
    alu0_scalar_nxt = '0;
    alu0_vector_en  = '0;
    alu0_vector_nxt = '0;
    for (int v = 0; v < VSIZE; v++)
    begin
      case (wr_typ[v][ALU0_WR_BASE])
      ot_s:
        begin
          if (v == 0)
          begin
            // write element  [0][0]
            alu0_scalar_en[wr_ad[0][ALU0_WR_BASE]]   |= ~stall;
            alu0_scalar_nxt[wr_ad[0][ALU0_WR_BASE]]  |= wr_data[ALU0_WR_BASE][0][0];
          end
        end
      ot_v:
        begin
          // write an entire vector
          alu0_vector_en[v][wr_ad[v][ALU0_WR_BASE]]  |= ~stall;
          alu0_vector_nxt[wr_ad[v][ALU0_WR_BASE]][v] |= wr_data[ALU0_WR_BASE][v];
        end
// spyglass disable_block W193
//SMD:Empty statement
//SJ :intentional default
      default:; // ignore
// spyglass enable_block W193
      endcase // case (wr_typ[v][ALU0_WR_BASE])
    end
  end : alu0_wr_PROC
  
  // other FU write
  always_comb
  begin : other_wr_PROC
    // defaults
    other_scalar_nxt = '0;
    other_vector_nxt = '0;
    other_scalar_en  = '0;
    other_vector_en  = '0;
    wr_ill           = 1'b0;
    for (int p = 0; p < NWR; p++)
    begin
      if (p != ALU0_WR_BASE)
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          case (wr_typ[v][p])
          ot_s:
            begin
              if (v == 0)
              begin
                if ((SWR&(1<<p)) != 0)
                begin
                  // write element  [0][0]
                  other_scalar_en[wr_ad[0][p]]  |= ~stall;
                  other_scalar_nxt[wr_ad[0][p]] |= wr_data[p][0][0];
                end
                else
                begin
                  // illegal scalar port
                  wr_ill[p] = 1'b1;
                end
              end
            end
          ot_v:
            begin
              // write an entire vector
              other_vector_en[v][wr_ad[v][p]]  |= ~stall;
              other_vector_nxt[wr_ad[v][p]][v] |= wr_data[p][v];
            end
// spyglass disable_block W193
//SMD:Empty statement
//SJ :intentional default
          default:; // ignore
// spyglass enable_block W193
          endcase // case (wr_typ[0][p])
        end
      end
    end
  end : other_wr_PROC
  
  // register next state and enable
  assign scalar_en  = hlp_scalar_en    | alu0_scalar_en  | other_scalar_en;
  assign scalar_nxt = hlp_scalar_nxt   | alu0_scalar_nxt | other_scalar_nxt;
  assign vector_en  = trnsp_vector_en  | alu0_vector_en  | other_vector_en;
  assign vector_nxt = trnsp_vector_nxt | alu0_vector_nxt | other_vector_nxt;


  // state registers
  // outputs: scalar_r, vector_r, bpar_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      scalar_r  <= '0;
      vector_r  <= '0;
      bpar_r    <= '0;
    end
    else
    begin
      for (int r = 0; r < ACT_SREG_NUM; r++)
      begin
        if (scalar_en[r])
        begin
          scalar_r[r]   <= scalar_nxt[r];
        end
      end
      for (int v = 0; v < VSIZE; v++)
        begin
          for (int r = 0; r < ACT_VREG_NUM; r++)
            if (vector_en[v][r])
            begin
              vector_r[r][v] <= vector_nxt[r][v];
            end
        end
      if (bpar_en)
      begin
        bpar_r          <= bpar_nxt;
      end
    end
  end : state_reg_PROC

  
`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_pars;
  @(posedge rst_a) ACT_BREG_NUM <= 16 && ACT_SREG_NUM <= 8 && ACT_VREG_NUM <= 8;
  endproperty : prop_pars
  a_pars: assert property (prop_pars) else $fatal(1, "Error:parameter error");
  property prop_ill_rd;
  @(posedge clk) disable iff (rst_a !== 1'b0) ~stall |-> rd_ill == '0;
  endproperty : prop_ill_rd
  a_ill_rd: assert property (prop_ill_rd) else $fatal(1, "Error: illegal read operand on port");
  property prop_ill_wr;
  @(posedge clk) disable iff (rst_a !== 1'b0) ~stall |-> wr_ill == '0;
  endproperty : prop_ill_wr
  a_ill_wr: assert property (prop_ill_wr) else $fatal(1, "Error: illegal write operand on port");
`endif
                  
endmodule : npu_gtoa_rf
