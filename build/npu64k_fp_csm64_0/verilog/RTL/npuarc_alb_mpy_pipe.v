// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2013-2014 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//--+----1----+----2----+----3----+----4----+----5----+----6----+----7----+----8
//
//
//   #     #  ######   #     #         ######   ###  ######   #######
//   ##   ##  #     #   #   #          #     #   #   #     #  #
//   # # # #  #     #    # #           #     #   #   #     #  #
//   #  #  #  ######      #            ######    #   ######   #####
//   #     #  #           #            #         #   #        #
//   #     #  #           #            #         #   #        #
//   #     #  #           #  ########  #        ###  #        #######
//
//
// Description:
//
//  This module implements all the multiply, madd and mac operations.
//  It also passes data to MP4 adder for vector add/sub operations.
//  The main code of the divide logic is based on the EM implementation with
//  The mpy module is operating in lock-step with the HS EXU pipeline.
//  Pipe flush and stall is directly under external control.
//  
//  Vector add/sub instruction pass data through the mpy pipe to the CA adder.
//  Those instructions are identified by: xx_vector_op_r & ~xx_mpy_op_r 
//  
//  Accumulator operations always result in 64-bits.
//  The data path is split. The high bits (63:32) are registered in the mpy
//  pipe at the end of mp3 and go out to the 64-bit adder in mp4. The lower
//  bits (31:0) are merged into the main EXU path at the end of mp3 and are
//  registered in the common data path outside the mpy pipe.
//  
//  Accumulator bypass with back-to-back MAC and no stalls is computed in mp3 
//  by looking at valid instruction in mp4 with acc target.
//  Note that vector add/sub do not target the acc, therefore we only have
//  add relation between the redundant internal (high) sum and carry in mp4.
//  
//  Accumulator bypass from x4 to mp3 is also possible for fpu instructions.
//  Any such "raw" conflict will be considered in the global EXU pipe control
//  and stall the mp3 instruction, if required.
//  Because of this convention, the mpy pipe logic does not consider external
//  bypass. It only resolves a madd/mac in mp4 with a pending madd/mac in mp3
//  to enable the internal bypass (see exu specification document).
//  
// ===========================================================================
//

// Configuration-dependent macro definitions
//

// Set simulation timescale
//
//`timescale 1 ns / 10 ps
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on

`ifdef VERILATOR
`define INFER_MPY_LOCAL
`else
`undef INFER_MPY_LOCAL
`endif

 
//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_mpy_pipe (
  ////////// General input signals /////////////////////////////////////////////
  //
  input                  clk,             // Clock input
  input                  rst_a,           // Asynchronous reset input

  //////// Interfaces from EXU to the multiplier module ////////////////////////
  //
  ////////// Dispatch Interface ////////////////////////////////////////////////
  // MP1 interface (aligned with X1)
  //
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  exu interface
  input                  x1_pass,         // X1 instr ready to go to X2
  input                  x1_mpy_op_r,     // mpy op is dispatched from X1
// spyglass disable_block W240
// SMD: non driving port
// SJ:  standard signal mpy interface
  input                  x1_half_size_r,  // scalar operand is 16 bits
// spyglass enable_block W240
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  standard signal mpy interface, may not be used in some configs
  input                  x1_dual_op_r,    // dual SIMD operation
// spyglass enable_block W240
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  standard signal mpy interface, may not be used in some configs
  input                  x1_vector_op_r,  // independent channels
// spyglass enable_block W240
// spyglass disable_block W240
// SMD: Input declared but not read
// SJ:  Unused ports, left for interface consistency vs spec
  input                  x1_quad_op_r,    // quad SIMD operation
// spyglass enable_block W240
// leda NTL_CON13C on
// leda NTL_CON37 on
  input   [31:0]  mp1_src0_nxt,    // 1st src operand (lsb 32 bits)
  input   [31:0]  mp1_src1_nxt,    // 2nd src operand (lsb 32 bits)
  input   [31:0]  mp1_src2_nxt,    // 1st src operand (lsb 32 bits)
  input   [31:0]  mp1_src3_nxt,    // 2nd src operand (lsb 32 bits)

  // MP2 interface (aligned with X2)
  //
  input                  x2_enable,       // X2 can accept X1 instruction
  input                  x2_pass,         // X2 instr ready to go to X3
  input                  x2_mpy_op_r,     // mpy op in X2
  input                  x2_signed_op_r,  // mpy operation is signed
  input                  x2_half_size_r,  // scalar operand is 16 bits
  input                  x2_dual_op_r,    // dual SIMD operation
  input                  x2_vector_op_r,  // independent channels
  input                  x2_quad_op_r,    // quad SIMD operation

  // MP3 interface (aligned with X3)
  //
  input                  x3_enable,       // X3 can accept X2 instruction
  input                  x3_pass,         // X3 instr ready to go to CA
  input                  x3_mpy_op_r,     // mpy op in X3
// spyglass disable_block W240
// SMD: non driving port
// SJ:  standard signal mpy interface
  input                  x3_half_size_r,  // scalar operand is 16 bits
// spyglass enable_block W240

  output [31:0]   mp3_s_lo,        // mp3 sum lsb 32 bits, unreg
  output [31:0]   mp3_c_lo,        // mp3 carry lsb 32 bits, unreg

  input                  x3_acc_op_r,     // accumulate operation
  input                  x3_dual_op_r,    // dual SIMD operation
  input                  x3_vector_op_r,  // independent channels
  input                  x3_quad_op_r,    // quad SIMD operation

  // MP4 interface (aligned with CA)
  //
  input                  ca_enable,       // CA can accept X3 instruction
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Arithmetic module
  output reg [31:0] mp4_s_hi_r,    // mp4 sum msb 32 bits, reg
  output reg [31:0] mp4_c_hi_r,    // mp4 carry msb 32 bits, reg
  output reg             mp4_s_65_r,      // additional bit for macu ovf, reg
  output reg             mp4_c_65_r,      // additional bit for macu ovf, reg
  // leda NTL_CON32 on
  input   [31:0]  ca_src0_r,       // mp4 sum lsb 32 bits, reg
  input   [31:0]  ca_src1_r,       // mp4 carry lsb 32 bits, reg
  input                  sel_byp_acc,     // from exu pipe control
  input   [31:0]  byp_acc_lo,      // ACCL value from regfile or WA
  input   [31:0]  byp_acc_hi,      // ACCH value from regfile or WA

  // Unit-level clock-gating input control signals from SA
  //
  input                  sa_mpy_op_r,     // MPY operation wakes up mpy pipe
  input                  sa_vector_op_r,  // vector op wakes up mpy pipe,
  input                  sa_half_size_r,  //  if type of vector op requires
  input                  sa_dual_op_r,    //  operands to pass through mpy pipe

  // Unit-level clock-gating output control signal to clock_ctrl module
  //
  output reg             mpy_unit_enable, // clk for mpy_pipe required next cycle
  
  // WA interface (pipeline flush)
  //
// spyglass disable_block W240
// SMD: non driving port
// SJ:  standard signal wa interface
  input                  wa_restart_r     // flush pipeline from WA
// spyglass enable_block W240
);


// MP1 staging registers declaration

reg  [31:0]      mp2_src0_r;
reg  [31:0]      mp2_src1_r;
reg  [31:0]      mp2_src2_r;
reg  [31:0]      mp2_src3_r;

// Unit-level clock-gating control signal declarations
//
reg                     sa_mpy_wakeup;  // re-enable mpy_clk if MPY op in SA
reg                     x1_mpy_active;  // keep mpy_clk active if MPY op in X1
reg                     x2_mpy_active;  // keep mpy_clk active if MPY op in X1
reg                     x3_mpy_active;  // keep mpy_clk active if MPY op in X1

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic to determine when the clock can be turned off to the //
// multiplier pipeline (mpy_unit_idle) and when it must be turned on again  //
// (mpy_unit_enable).                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: mpy_clk_ctrl_PROC

  sa_mpy_wakeup   = (   sa_mpy_op_r
                      | sa_vector_op_r & (sa_half_size_r ^ sa_dual_op_r));

  x1_mpy_active   = (   x1_mpy_op_r
                      | x1_vector_op_r & (x1_half_size_r ^ x1_dual_op_r));

  x2_mpy_active   = (   x2_mpy_op_r
                      | x2_vector_op_r & (x2_half_size_r ^ x2_dual_op_r));

  x3_mpy_active   = (   x3_mpy_op_r
                      | x3_vector_op_r & (x3_half_size_r ^ x3_dual_op_r));

  
  mpy_unit_enable = sa_mpy_wakeup
                  | x1_mpy_active
                  | x2_mpy_active
                  | x3_mpy_active
                  ;
  
end // mpy_clk_ctrl_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Register incoming data only, late in X1                                  //
// Note that instruction attributes are input from exu at each pipe stage   //
//   and therefore are not included in the input register logic             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire  x1_data_ready_cg0;
assign x1_data_ready_cg0 = x1_pass & x2_enable &
       ( x1_mpy_op_r     |                                   // mpy, vmpy2h
         x1_vector_op_r & (x1_half_size_r ^ x1_dual_op_r));  // pass-through

// leda NTL_RST03 off
// LMD: flop without reset
// LJ:  data only flop, no reset needed
// leda S_1C_R off
// LMD: flop without reset
// LJ:  data only flop, no reset needed
// spyglass disable_block Clock_info03a
// SMD: clock-net unconstrained
// SJ:  is constrained
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: input_data_PROC
if (x1_data_ready_cg0 == 1'b1)
  begin
    mp2_src0_r      <=  mp1_src0_nxt;
    mp2_src1_r      <=  mp1_src1_nxt;
    mp2_src2_r      <=  mp1_src2_nxt;
    mp2_src3_r      <=  mp1_src3_nxt;
  end
end  // input_data_PROC
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block Clock_info03a
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

// Aliases
// Input data is split into 16-bit quantities, naming follows spec document

wire  [15: 0]          src_operand_a0;
assign src_operand_a0 = mp2_src0_r[15: 0];
wire  [15: 0]          src_operand_b0;
assign src_operand_b0 = mp2_src1_r[15: 0];
wire  [31:16]          src_operand_a1;
assign src_operand_a1 = mp2_src0_r[31:16];
wire  [31:16]          src_operand_b1;
assign src_operand_b1 = mp2_src1_r[31:16];

wire  [15: 0]          src_operand_a2;
assign src_operand_a2 = mp2_src2_r[15: 0];
wire  [15: 0]          src_operand_b2;
assign src_operand_b2 = mp2_src3_r[15: 0];
wire  [31:16]          src_operand_a3;
assign src_operand_a3 = mp2_src2_r[31:16];
wire  [31:16]          src_operand_b3;
assign src_operand_b3 = mp2_src3_r[31:16];

///////////////////////////////////////////////////////////////////////////////
//  MP2 declarations                                                         //
///////////////////////////////////////////////////////////////////////////////

wire  [34:0]           mul0_sum;            // output - sum
wire  [34:0]           mul0_cy;             // output - carry
reg   [15:0]           mul0_dataa;          // input - multiplier
reg   [15:0]           mul0_datab;          // input - multiplicand
reg                    mul0_signed_op_a;
reg                    mul0_signed_op_b;

reg   [34:0]           mp3_s0_r;            // staging registers 
reg   [34:0]           mp3_c0_r;

wire  [34:0]           mul1_sum;            // output - sum
wire  [34:0]           mul1_cy;             // output - carry
reg   [15:0]           mul1_dataa;          // input - multiplier
reg   [15:0]           mul1_datab;          // input - multiplicand
reg                    mul1_signed_op_a;
reg                    mul1_signed_op_b;

wire  [34:0]           mul2_sum;            // output - sum
wire  [34:0]           mul2_cy;             // output - carry
reg   [15:0]           mul2_dataa;          // input - multiplier
reg   [15:0]           mul2_datab;          // input - multiplicand
reg                    mul2_signed_op_a;
reg                    mul2_signed_op_b;

wire  [34:0]           mul3_sum;            // output - sum
wire  [34:0]           mul3_cy;             // output - carry
reg   [15:0]           mul3_dataa;          // input - multiplier
reg   [15:0]           mul3_datab;          // input - multiplicand
reg                    mul3_signed_op_a;
reg                    mul3_signed_op_b;
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Staging reg

reg   [34:0]           mp3_s1_r;            // staging registers
reg   [34:0]           mp3_c1_r;
reg   [34:0]           mp3_s2_r;
reg   [34:0]           mp3_c2_r;
reg   [34:0]           mp3_s3_r;
reg   [34:0]           mp3_c3_r;
  // leda NTL_CON32 on

///////////////////////////////////////////////////////////////////////////////
// MP2 LOGIC                                                                 //
///////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////////
// Decode instruction and steer data to 16x16 multipliers
// Different mpy_option use different interface signals and utilize different
// complexity of the MP3 compressor, so code varies significantly per option
//


always @(*)
begin:   opt9_data_PROC
casez ({x2_mpy_op_r,x2_half_size_r,x2_dual_op_r,x2_quad_op_r,x2_vector_op_r})
  
  5'b10000:    // MPY, MPYM, MAC, MPYD, MACD (template A)
    begin
      mul0_dataa = src_operand_a0;    mul0_signed_op_a = 1'b0;
      mul0_datab = src_operand_b0;    mul0_signed_op_b = 1'b0;

      mul1_dataa = src_operand_a1;    mul1_signed_op_a = x2_signed_op_r;
      mul1_datab = src_operand_b0;    mul1_signed_op_b = 1'b0;

      mul2_dataa = src_operand_a0;    mul2_signed_op_a = 1'b0;
      mul2_datab = src_operand_b1;    mul2_signed_op_b = x2_signed_op_r;

      mul3_dataa = src_operand_a1;    mul3_signed_op_a = x2_signed_op_r;
      mul3_datab = src_operand_b1;    mul3_signed_op_b = x2_signed_op_r;
    end 

  5'b11100,    // DMPYH, DMACH (template D)
  5'b11101:    // VMPY2H       (template E)
    begin      

      // calculate 16x16 product
      
      mul0_dataa = src_operand_a0;    mul0_signed_op_a = x2_signed_op_r;
      mul0_datab = src_operand_b0;    mul0_signed_op_b = x2_signed_op_r;
      
      mul3_dataa = src_operand_a1;    mul3_signed_op_a = x2_signed_op_r;
      mul3_datab = src_operand_b1;    mul3_signed_op_b = x2_signed_op_r;

      // zero out two products
      
      mul1_dataa =  16'h0;              mul1_signed_op_a = 1'b0;
      mul1_datab =  16'h0;              mul1_signed_op_b = 1'b0;

      mul2_dataa =  16'h0;              mul2_signed_op_a = 1'b0;
      mul2_datab =  16'h0;              mul2_signed_op_b = 1'b0;
    end 

  5'b01011,    // 64-bit Vector-add - pass through: VADD4H
  5'b00101:    // 64-bit Vector-add - pass through: VADD2
    begin      
      mul0_dataa = 16'h1;               mul0_signed_op_a = 1'b0;
      mul0_datab =  src_operand_a2;   mul0_signed_op_b = 1'b0;

      mul1_dataa = 16'h1;               mul1_signed_op_a = 1'b0;
      mul1_datab =  src_operand_a3;   mul1_signed_op_b = 1'b0;
      
      // note: pp2 and pp3 inputs swapped to unify compressor selection in mp3
      mul2_dataa = 16'h1;               mul2_signed_op_a = 1'b0;
      mul2_datab =  src_operand_b3;   mul2_signed_op_b = 1'b0;

      mul3_dataa = 16'h1;               mul3_signed_op_a = 1'b0;
      mul3_datab =  src_operand_b2;   mul3_signed_op_b = 1'b0;
    end 

  5'b10100:    // DMPYWH, DMACWH (template B)
    begin
      mul0_dataa = src_operand_a0;    mul0_signed_op_a = 1'b0;
      mul0_datab = src_operand_b0;    mul0_signed_op_b = x2_signed_op_r;

      mul1_dataa = src_operand_a1;    mul1_signed_op_a = x2_signed_op_r;
      mul1_datab = src_operand_b0;    mul1_signed_op_b = x2_signed_op_r;

      mul2_dataa = src_operand_a2;    mul2_signed_op_a = 1'b0;
      mul2_datab = src_operand_b1;    mul2_signed_op_b = x2_signed_op_r;

      mul3_dataa = src_operand_a3;    mul3_signed_op_a = x2_signed_op_r;
      mul3_datab = src_operand_b1;    mul3_signed_op_b = x2_signed_op_r;
    end 

  5'b11010:    // QMPYH, QMACH (template C)
    begin
      mul0_dataa = src_operand_a0;    mul0_signed_op_a = x2_signed_op_r;
      mul0_datab = src_operand_b0;    mul0_signed_op_b = x2_signed_op_r;

      mul1_dataa = src_operand_a3;    mul1_signed_op_a = x2_signed_op_r;
      mul1_datab = src_operand_b3;    mul1_signed_op_b = x2_signed_op_r;

      mul2_dataa = src_operand_a2;    mul2_signed_op_a = x2_signed_op_r;
      mul2_datab = src_operand_b2;    mul2_signed_op_b = x2_signed_op_r;

      mul3_dataa = src_operand_a1;    mul3_signed_op_a = x2_signed_op_r;
      mul3_datab = src_operand_b1;    mul3_signed_op_b = x2_signed_op_r;
    end 

  default:   // MPYW (template A, single pp)
    begin

      // calculate 16x16 product
      
      mul0_dataa = src_operand_a0;    mul0_signed_op_a = x2_signed_op_r;
      mul0_datab = src_operand_b0;    mul0_signed_op_b = x2_signed_op_r;
      
      // zero out all other products
      
      mul1_dataa =  16'h0;  mul1_signed_op_a = 1'b0;
      mul1_datab =  16'h0;  mul1_signed_op_b = 1'b0;

      mul2_dataa =  16'h0;  mul2_signed_op_a = 1'b0;
      mul2_datab =  16'h0;  mul2_signed_op_b = 1'b0;

      mul3_dataa =  16'h0;  mul3_signed_op_a = 1'b0;
      mul3_datab =  16'h0;  mul3_signed_op_b = 1'b0;
    end  
endcase
end


///////////////////////////////////////////////////////////////////////////////
// MP2 - 16x16 multipliers
//

`ifdef INFER_MPY_LOCAL
npuarc_mult16x16_cs35_infer u_MUL0(
`else
npuarc_mult16x16_cs35 u_MUL0(
`endif
           .res_sum     ( mul0_sum         ),
           .res_carry   ( mul0_cy          ),
           .dataa       ( mul0_dataa       ),
           .datab       ( mul0_datab       ),
           .signed_op_a ( mul0_signed_op_a ),
           .signed_op_b ( mul0_signed_op_b )
          );

`ifdef INFER_MPY_LOCAL
npuarc_mult16x16_cs35_infer u_MUL1(
`else
npuarc_mult16x16_cs35 u_MUL1(
`endif
           .res_sum     ( mul1_sum         ),
           .res_carry   ( mul1_cy          ),
           .dataa       ( mul1_dataa       ),
           .datab       ( mul1_datab       ),
           .signed_op_a ( mul1_signed_op_a ),
           .signed_op_b ( mul1_signed_op_b )
          );

`ifdef INFER_MPY_LOCAL
npuarc_mult16x16_cs35_infer u_MUL2(
`else
npuarc_mult16x16_cs35 u_MUL2(
`endif
           .res_sum     ( mul2_sum         ),
           .res_carry   ( mul2_cy          ),
           .dataa       ( mul2_dataa       ),
           .datab       ( mul2_datab       ),
           .signed_op_a ( mul2_signed_op_a ),
           .signed_op_b ( mul2_signed_op_b )
          );

`ifdef INFER_MPY_LOCAL
npuarc_mult16x16_cs35_infer u_MUL3(
`else
npuarc_mult16x16_cs35 u_MUL3(
`endif
           .res_sum     ( mul3_sum         ),
           .res_carry   ( mul3_cy          ),
           .dataa       ( mul3_dataa       ),
           .datab       ( mul3_datab       ),
           .signed_op_a ( mul3_signed_op_a ),
           .signed_op_b ( mul3_signed_op_b )
          );



///////////////////////////////////////////////////////////////////////////////
// Register output of MP2 multipliers
//

wire x2_sc_ready_cg0;
assign x2_sc_ready_cg0 = x2_pass & x3_enable &
       ( x2_mpy_op_r     |                                   // mpy, vmpy2h
         x2_vector_op_r & (x2_half_size_r ^ x2_dual_op_r));  // pass-through

// leda S_1C_R off
// LMD: flop without reset
// LJ:  data only flop, no reset needed
// leda NTL_RST03 off
// leda S_1C_R off
// LMD: flop without reset
// LJ:  data only flop, no reset needed
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: quad_pp_PROC
if (x2_sc_ready_cg0 == 1'b1)
  begin
    mp3_s0_r        <=   mul0_sum;
    mp3_c0_r        <=   mul0_cy;
    mp3_s1_r        <=   mul1_sum;
    mp3_c1_r        <=   mul1_cy;
    mp3_s2_r        <=   mul2_sum;
    mp3_c2_r        <=   mul2_cy;
    mp3_s3_r        <=   mul3_sum;
    mp3_c3_r        <=   mul3_cy;
  end
end  // quad_pp_PROC
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
///////////////////////////////////////////////////////////////////////////////
//  MP3 declarations                                                         //
///////////////////////////////////////////////////////////////////////////////

reg  [64:0]            pp0;       // inputs to compressor: multiplier and sext
reg  [64:0]            pp1;
reg  [64:0]            pp2;
reg  [64:0]            pp3;
reg  [64:0]            pp4;
reg  [64:0]            pp5;
reg  [64:0]            pp6;
reg  [64:0]            pp7;
reg  [64:0]            pp8;
reg  [64:0]            pp9;       // inputs to compressor: accumulator
reg  [64:0]            pp10;
wire [64:0]            pp1_0;     // outputs of level 1 CSA tree
wire [64:0]            pp1_1;
wire [64:0]            pp1_2;
wire [64:0]            pp1_3;
wire [64:0]            pp1_4;
wire [64:0]            pp1_5;

wire [64:0]            pp2_0;     // outputs of level 2 CSA tree
wire [64:0]            pp2_1;
wire [64:0]            pp2_2;
wire [64:0]            pp2_3;

wire [64:0]            pp3_0;     // outputs of level 3 CSA tree
wire [64:0]            pp3_1;

// accumulator mux outputs
reg  [31:0]     acc_s_lo;
reg  [31:0]     acc_s_hi;
reg                    acc_s_65;
reg  [31:0]     acc_c_lo;  // note that the _c_ components are set to
reg  [31:0]     acc_c_hi;  // zero when selecting external bypass
reg                    acc_c_65;

///////////////////////////////////////////////////////////////////////////////
// MP3 LOGIC                                                                 //
///////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////////
// Decode instruction and steer data multiplier output data (registered) to
// the appropriate compressor to achieve functionality.
// Implementation of same instructions may vary slightly per mpy_option
//


///////////////////////////////////////////////////////////////////////////////
// Accumulator Datapath
// EXU pipe control determines if the bypass is internal to the mpy_pipe (from
// mp4 staging to mp3 compressor logic, in redundant sum/carry form) or external
// (from register file, not redundant).
// 

always@(*)
begin:   opt6_acc_PROC
casez ({x3_acc_op_r, sel_byp_acc})
  2'b0?:
    begin                // not a MAC op
     acc_s_lo = 32'h0; 
     acc_s_hi = 32'h0; 
     acc_s_65 = 1'b0; 
     acc_c_lo = 32'h0; 
     acc_c_hi = 32'h0; 
     acc_c_65 = 1'b0; 
    end  
  2'b10:
    begin                // MAC, int bypass of redundant s/c
     acc_s_lo = ca_src0_r; 
     acc_s_hi = mp4_s_hi_r; 
     acc_s_65 = mp4_s_65_r; // mp4_s_hi_r[31];    // sign extend
     acc_c_lo = ca_src1_r; 
     acc_c_hi = mp4_c_hi_r; 
     acc_c_65 = mp4_c_65_r; // mp4_c_hi_r[31];    // sign extend
    end  
  default:
    begin                // 2'b11: MAC, ext bypass of non-redundant acc
     acc_s_lo = byp_acc_lo;
     acc_s_hi = byp_acc_hi;
     acc_s_65 = 1'b0;    // zero extend - used only for MACU ovf detection
     acc_c_lo = 32'h0; 
     acc_c_hi = 32'h0; 
     acc_c_65 = 1'b0; 
    end  
endcase
end

///////////////////////////////////////////////////////////////////////////////
// Input muxing to the mpy_option 9 compressor
// Assembles 11 pps from the 4 multipliers sum/carry with sign extension logic

always @(*)
begin:   opt9_pp_PROC
casez ({x3_mpy_op_r,x3_half_size_r,x3_dual_op_r,x3_quad_op_r,x3_vector_op_r})
  
  5'b10000,    // MPY, MPYM, MAC, MPYD, MACD (template A)
  5'b11000:    // MPYW                       (template A, pp2-10 are zero)
    begin
      // template A
      pp0  = {29'h0, ~mp3_s0_r[34], mp3_s0_r[34:0]};
      pp1  = {29'h0, ~mp3_c0_r[34], mp3_c0_r[34:0]};

      pp2  = {13'h0, ~mp3_s1_r[34], mp3_s1_r[34:0], 16'h0};
      pp3  = {13'h0, ~mp3_c1_r[34], mp3_c1_r[34:0], 16'h0}; 

      pp4  = {13'h0, ~mp3_s2_r[34], mp3_s2_r[34:0], 16'h0};
      pp5  = {13'h0, ~mp3_c2_r[34], mp3_c2_r[34:0], 16'h0}; 

      // s3/c3 upper bits overflow the result field [63:0], therefore truncated
      pp6  = {mp3_s3_r[32:0], 32'h0};
      pp7  = {mp3_c3_r[32:0], 32'h0}; 

      // accumulator is zero value for option 7 template A instructions
      pp8  = {acc_s_65, acc_s_hi, acc_s_lo};
      pp9  = {acc_c_65, acc_c_hi, acc_c_lo}; 

      // sign extension constant
      pp10 = {30'h3ffb_fffe, 35'h0};                  // sext const, template A
    end 

  5'b11100:    // DMPYH, DMACH (template D)
    begin      
      pp0  = {29'h0, ~mp3_s0_r[34], mp3_s0_r[34:0]};
      pp1  = {29'h0, ~mp3_c0_r[34], mp3_c0_r[34:0]};

      pp2  = {13'h0, ~mp3_s1_r[34], mp3_s1_r[34:0], 16'h0};  // fake mid product
      pp3  = {13'h0, ~mp3_c1_r[34], mp3_c1_r[34:0], 16'h0};  // both eq zero

      pp4  = {13'h0, ~mp3_s2_r[34], mp3_s2_r[34:0], 16'h0};  // fake mid product
      pp5  = {13'h0, ~mp3_c2_r[34], mp3_c2_r[34:0], 16'h0};  // both eq zero 

      pp6  = {29'h0, ~mp3_s3_r[34], mp3_s3_r[34:0]};
      pp7  = {29'h0, ~mp3_c3_r[34], mp3_c3_r[34:0]};

      // accumulator is pre-calculated including zero and external bypass
      pp8  = {acc_s_65, acc_s_hi, acc_s_lo};
      pp9  = {acc_c_65, acc_c_hi, acc_c_lo}; 

      // sign extension constant
      pp10 = {30'h1ffb_fffc, 35'h0};                  // sext const, template D
    end 

  5'b11101:    // VMPY2H       (template E)
    begin      
      // 16x16 is aligned at the acc half
      // Upper result taken from compressor stage 1
      // Lower result taken from compressor out (more critical path)
      // sign extension not needed but kept for simlification
      pp0  = {29'h0, ~mp3_s0_r[34], mp3_s0_r[34:0]};
      pp1  = {29'h0, ~mp3_c0_r[34], mp3_c0_r[34:0]};

      pp2  = 65'h0;
      pp3  = 65'h0;

      pp4  = {acc_s_65, acc_s_hi, 32'h0};  // acc hi
      pp5  = {acc_c_65, acc_c_hi, 32'h0}; 

      pp6  = {mp3_s3_r[31], mp3_s3_r[31:0], 32'h0};
      pp7  = {mp3_c3_r[31], mp3_c3_r[31:0], 32'h0};

      // accumulator, lower half adds with pp0/1, higher half is a dont_care
      pp8  = {acc_s_65, acc_s_hi, acc_s_lo};
      pp9  = {acc_c_65, acc_c_hi, acc_c_lo}; 

      // sign ext constant - lower 32-bit set to zero so lower result is correct
      pp10 = {30'h1ffb_fffc, 35'h0};
    end 

  5'b10100:    // DMPYWH, DMACWH (template B)
    begin
      pp0  = {29'h0, ~mp3_s0_r[34], mp3_s0_r[34:0]};
      pp1  = {29'h0, ~mp3_c0_r[34], mp3_c0_r[34:0]};

      pp2  = {13'h0, ~mp3_s1_r[34], mp3_s1_r[34:0], 16'h0};
      pp3  = {13'h0, ~mp3_c1_r[34], mp3_c1_r[34:0], 16'h0}; 

      pp4  = {29'h0, ~mp3_s2_r[34], mp3_s2_r[34:0]};
      pp5  = {29'h0, ~mp3_c2_r[34], mp3_c2_r[34:0]}; 

      pp6  = {13'h0, ~mp3_s3_r[34], mp3_s3_r[34:0], 16'h0};
      pp7  = {13'h0, ~mp3_c3_r[34], mp3_c3_r[34:0], 16'h0};  

      // accumulator
      pp8  = {acc_s_65, acc_s_hi, acc_s_lo};
      pp9  = {acc_c_65, acc_c_hi, acc_c_lo}; 

      // sign extension constant
      pp10 = {30'h1ffb_fffc, 35'h0};
    end 

  5'b11010:    // QMPYH, QMACH (template C)
    begin
      pp0  = {29'h0, ~mp3_s0_r[34], mp3_s0_r[34:0]};
      pp1  = {29'h0, ~mp3_c0_r[34], mp3_c0_r[34:0]};

      pp2  = {29'h0, ~mp3_s1_r[34], mp3_s1_r[34:0]};
      pp3  = {29'h0, ~mp3_c1_r[34], mp3_c1_r[34:0]}; 

      pp4  = {29'h0, ~mp3_s2_r[34], mp3_s2_r[34:0]};
      pp5  = {29'h0, ~mp3_c2_r[34], mp3_c2_r[34:0]}; 

      pp6  = {29'h0, ~mp3_s3_r[34], mp3_s3_r[34:0]};
      pp7  = {29'h0, ~mp3_c3_r[34], mp3_c3_r[34:0]};  

      // accumulator
      pp8  = {acc_s_65, acc_s_hi, acc_s_lo};
      pp9  = {acc_c_65, acc_c_hi, acc_c_lo}; 

      // sign extension constant
      pp10 = {30'h1fff_fff8, 35'h0};
    end 

  default:    // Vector add - pass through
    begin      
      // Individual 16 bits were multiplied unsigned by 1 in mp2.
      // They are assembled through the compressor to avoid another mux input
      // for the result.
      // There are no overlapping fields to guaranty no carry, therefore sum
      // component is the correct pass-through data to CA adder.
      pp0  = {49'h0, mp3_s0_r[15:0]};
      pp1  = {49'h0, mp3_c0_r[15:0]};

      pp2  = {33'h0, mp3_s1_r[15:0], 16'h0};
      pp3  = {33'h0, mp3_c1_r[15:0], 16'h0};

      pp4  = {mp3_s2_r[15], mp3_s2_r[15:0], 48'h0};
      pp5  = {mp3_c2_r[15], mp3_c2_r[15:0], 48'h0};

      pp6  = {17'h0, mp3_s3_r[15:0], 32'h0};
      pp7  = {17'h0, mp3_c3_r[15:0], 32'h0}; 

      // accumulator is guaranteed zero
      pp8  = {acc_s_65, acc_s_hi, acc_s_lo};
      pp9  = {acc_c_65, acc_c_hi, acc_c_lo}; 

      // sign extension constant
      pp10 = 65'h0; // sext const, template F - sum component is correct as-is
    end 

endcase
end

///////////////////////////////////////////////////////////////////////////////
// Compressor, stage 1: 11 pps implemented as two 4:2 and one 3:2  ->  6 pps
// Note that inputs are specified as 64 bit, but constants reduce in synthesis.
// Logic chops data beyond 64 bits (insignificant arithmetic overflow).
// 
// Inputs:  pp0 through pp10
// Outputs: pp1_0, pp1_1, pp1_2, pp1_3, pp1_4, pp1_5
// 

npuarc_csa_4_2_64 u_U1_0(
                .di0   ( pp0   ),
                .di1   ( pp1   ),
                .di2   ( pp2   ),
                .di3   ( pp3   ),
  
                .sum   ( pp1_0 ),
                .carry ( pp1_1 )
 );

npuarc_csa_4_2_64 u_U1_1(
                .di0   ( pp4   ),
                .di1   ( pp5   ),
                .di2   ( pp6   ),
                .di3   ( pp7   ),
  
                .sum   ( pp1_2 ),
                .carry ( pp1_3 )
 );

npuarc_csa_3_2_64 u_U1_2(
                .di0   ( pp8   ),
                .di1   ( pp9   ),
                .di2   ( pp10  ),
  
                .sum   ( pp1_4 ),
                .carry ( pp1_5 )
 );


///////////////////////////////////////////////////////////////////////////////
// Compressor, stage 2: 6 pps implemented as two 3:2  ->  4 pps
// 
// Inputs:  pp1_0,pp1_1,pp1_2,pp1_3,pp1_4,pp1_5
// Outputs: pp2_0, pp2_1,pp2_2, pp2_3
// 

npuarc_csa_3_2_64 u_U2_0(
                .di0   ( pp1_0 ),
                .di1   ( pp1_1 ),
                .di2   ( pp1_2 ),
  
                .sum   ( pp2_0 ),
                .carry ( pp2_1 )
 );

npuarc_csa_3_2_64 u_U2_1(
                .di0   ( pp1_3 ),
                .di1   ( pp1_4 ),
                .di2   ( pp1_5 ),
  
                .sum   ( pp2_2 ),
                .carry ( pp2_3 )
 );


//////////////////////////////////////////////////////////////////////////////
// Compressor, stage 3: 4 pps into 4:2 ->  2 pps
// 
// Inputs:  pp2_0,pp2_1,pp2_2,pp2_3
// Outputs: pp3_0, pp3_1
// 

npuarc_csa_4_2_64 u_U3_0(
                .di0   ( pp2_0 ),
                .di1   ( pp2_1 ),
                .di2   ( pp2_2 ),
                .di3   ( pp2_3 ),
  
                .sum   ( pp3_0 ),
                .carry ( pp3_1 )
 );


//////////////////////////////////////////////////////////////////////////////
// Output Logic
// 

// unregistered low 32-bit outputs to X3 datapath
// Lower result is correct through the compressor even for VMPY2H
assign  mp3_s_lo = pp3_0[31:0];
assign  mp3_c_lo = pp3_1[31:0];

wire x3_sc_hi_ready_cg0;
assign x3_sc_hi_ready_cg0 = x3_pass & ca_enable &
       ( x3_mpy_op_r     |                                   // mpy, vmpy2h
         x3_vector_op_r & (x3_half_size_r ^ x3_dual_op_r));  // pass-through

// Registered high 32-bit outputs to X4 high adder
// x3_mpy_op_r & x3_vector_op_r: VMPY2H, high result taken from stage 1
always @(posedge clk or posedge rst_a)
begin: mp4_hi_reg_PROC
  if (rst_a == 1'b1)
    begin
    mp4_s_hi_r  <=  32'd0;
    mp4_s_65_r  <=  1'b0;
    mp4_c_hi_r  <=  32'd0;
    mp4_c_65_r  <=  1'b0;
    end
  else if (x3_sc_hi_ready_cg0)
    begin
    mp4_c_hi_r  <=  x3_vector_op_r ? pp1_2[63:32] : pp3_0[63:32];
    mp4_c_65_r  <=  pp3_0[64];    // for macu ovf only
    
    mp4_s_hi_r  <=  x3_vector_op_r
                    ?  (x3_mpy_op_r ? pp1_3[63:32] : pp1_0[31:0])
                    :  pp3_1[63:32]
                      ;
    mp4_s_65_r  <=  pp3_1[64];    // for macu ovf only

    end
end  // mp4_hi_reg_PROC

endmodule
