// Library ARCv2HS-3.5.999999999
//--+----1----+----2----+----3----+----4----+----5----+----6----+----7----+----8
//
// Copyright (C) 2011-2016 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary work of 
// Synopsys, Inc., and is fully protected under copyright and trade secret
// laws. You may not view, use, disclose, copy, or distribute this file or
// any information contained herein except pursuant to a valid written 
// license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//
//   #####   ###  #     #       ######   ###  ######   #######
//   #    #   #   #     #       #     #   #   #     #  #
//   #     #  #   #     #       #     #   #   #     #  #
//   #     #  #   #     #       ######    #   ######   #####
//   #     #  #    #   #        #         #   #        #
//   #    #   #     # #         #         #   #        #
//   #####   ###     #    ####  #        ###  #        #######
//
// Description:
//
//  This module optionally implements a fast radix-4 integer divide/remainder
//  logic (the only div/rem option for HS).
//  The main code of the divide logic is based on the EM implementation with
//  sequencer mods to improve timing at startup and correction steps. This
//  computational logic is sequenced by a "free-running" fd_state.
//  The interface to the HS EXU pipeline is implemented in a separate pt_state
//  state-machine, which handles the graduate/retire protocol, pipe flush and
//  stalls.
//  Decoupling the divide logic from pipeline tracking logic makes it possible
//  for the divide computations to run ahead or lag behind the EXU pipeline.
//  Once started, the result computation completes without any stalls. 
//
//  Updated Oct 2016: modified logic for divf with Q.31 operands.
//  This requires bypassing the exp logic and res_fraction logic and fixing
//  the step count to yield a 32-bit Q.31 result.
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command line such as:
//
//   vpp +q +o alb_div_pipe.vpp
//
// ===========================================================================
//

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

// include alu defines
//
// `include "dsp_reuse_defs.v"
// `include "dsp_alu_defines.v"
// `include "dsp_divf_defines_fake.v"
 

//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_div_pipe (


  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // Clock input
  input                       rst_a,            // Asynchronous reset input

  ////////// Dispatch Interface //////////////////////////////////////////////
  // assigns a new div operation to the divider
  //
  // instruction handshake
  output reg                  div_busy_r,       // div cannot accept instr
  input                       x1_pass,          // X1 instr ready to go to X2
  input                       x1_cond,          // X1 instr predicate
  input                       x2_enable,        // X2 can accept X1 instr
  // instruction details
  input                       sa_div_op_r,      // SA instr is div/rem
  input                       x1_div_op_r,      // X1 instr is div/rem
  input                       x1_div_kind_r,    // 0 => div/u, 1 => rem/u
  input                       x1_signed_op_r,   // X1 operand type is signed
  input                       x2_div_op_r,      // DIV,REM insn at X2 stage
  input   [`npuarc_DATA_RANGE]       x2_src0_nxt,      // source operand: dividend
  input   [`npuarc_DATA_RANGE]       x2_src1_nxt,      // source operand: divisor
  input                       x3_div_op_r,      // DIV,REM insn at X3 stage

  ////////// Instruction progression interface ///////////////////////////////
  // pipe control status signals, indicating commit and flush actions ////////
  //
  input                       x2_kill,          // kill instruction at X2
  input                       x3_kill,          // kill instruction at X3
  input                       ca_kill,          // kill instruction at CA
  input                       ca_div_op_r,      // div/rem has reached CA
  input                       ca_commit,        // CA instruction shall commit
  input                       ca_predicate_r,   // CA predicate value

  ////////// Unit-level clock gating control output to clock_ctrl ////////////
  //
  output                      div_unit_enable,  // clk ctrl for divider

  // Early indication of divide-by-zero //////////////////////////////////////
  //
  // div_divz early status signal:
  // valid prior to commit stage, so exception logic can consider it early
  // remains valid until instruction retires (no exception) or flushed
  //   div_divz = 1: divide by zero attempted, result and flags are not valid 
  //   div_divz = 0: successful completion, result and flags are valid 
  //
  output reg                  div_divz_r,       // Division by zero attempted

  ////////////////////////////////////////////////////////////////////////////
  // Divide logic always uses a graduate/retire interface, even if the result
  // is ready to retire at the commit stage (due to other EXU stalls)
  //////////////////////////////////////////////////////////////////////////// 
  
  ////////// Graduation Interface ////////////////////////////////////////////
  // Divide commits at the CA stage and receives a graduation tag.
  // Divide instruction is committed upon receiving the ca_commit signal.
  // If ca_div_grad_ack is not asserted on commit, then no result is produced.
  // After graduation, a div/rem instruction cannot be aborted.
  //
  output                      div_grad_req,     // grad without retirement
  input                       ca_div_grad_ack,  // grad ack
  input   [`npuarc_GRAD_TAG_RANGE]   ca_div_grad_tag,  // tag of graduating context  

  ////////// Retirement Interface ////////////////////////////////////////////
  // Retirement interface for post-commit divider result write-back //////////
  //
  output reg                  div_retire_req_r,     // retirement request 
  output reg [`npuarc_GRAD_TAG_RANGE]div_retire_tag_r,     // tag of retiring instr
  input                       ca_div_retire_ack,    // retirement ack
  // result data
  output reg [`npuarc_DATA_RANGE]    div_retire_result_r,  // result of div/rem
  // result flags
  output                      div_retire_overflow_r,// overflow status
  output                      div_retire_sign_r,    // sign status
  output                      div_retire_zero_r     // zero status

);


// Divider input registers
//
// Expanded input data regs to 34-bit, replacing P and D for divide
//
// leda N_10P_R_C off
// leda N_10P_R_D off
// LMD: allow upper-case in reg/wire name
// LJ:  uppercase is not replicated in lowercase, important for readability

reg   [`npuarc_DATA_RANGE]     x2_src0_r;          // 32-bit dividend, registered
reg   [`npuarc_DATA_RANGE]     x2_src1_r;          // 32-bit divisor,  registered
reg                     div_is_signed;      // signed operation
reg                     kind_is_div;        // divide operation (0 = rem)
reg                     kind_is_divf;       // fractional divide operation

wire                    div_in_x1;          // early start_div
wire                    div_is_commiting;   // exu promotes div past CA

reg   [33:0]            p_tmp_r;
reg   [33:0]            d_tmp_r;




// Div/Rem instruction control bits
//

// Result/accumulator register
//
reg   [67:0]            div_result_r;       // expanded to 2x34-bit for Q/Qn


///////////////////////////////////////////////////////////////////////////////
// Internal signal declarations                                              //
///////////////////////////////////////////////////////////////////////////////

reg                     div_ovf_r;

///////////////////////////////////////////////////////////////////////////////
// signals and params for the divide logic                                   //
///////////////////////////////////////////////////////////////////////////////

// Input stage

wire   [6:0]    src1_ffs, src2_ffs;     // first significant bit position
wire            src1_zero, src2_zero,   // flags
                src2_minus_1,
                src1_max_neg;
                
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used signal from arithmetic module
wire            src1_minus_1,
                src2_max_neg;
// leda NTL_CON13A on
reg    [6:0]    exp;                    // registered
reg             src1_zero_r;            // registered

reg             dividend_sign;          // needed for remainder logic
reg             quo_sign;               // sign of final quotient
wire            res_fraction;           // result is a fraction if exp < 0

wire            do_radix4_steps;
wire            do_radix2_step;

reg             x3_div_op_re;           // div/divu instruction, explicit code
                                        // (after decoding div_kind), not the
                                        // same as input ca_div_op_r !!!
reg             x3_rem_op_re;           // rem/remu instruction, explicit code
                                        // (after decoding div_kind)
reg             x3_divf_op_re;          // divf instruction, explicit code

wire  [32:0]    src0_extended;          // sign or zero extended, so that the
wire  [32:0]    src1_extended;          //   divide operation is always signed

// mux and register P (or N) and D

reg   [33:0]    p_pre;                  // see D description
wire  [33:0]    d_pre;                  // see P description
wire  [33:0]    p;                      // registers dividend N or partial
                                        // remainder P'
wire  [33:0]    d;                      // registers divisor D or
                                        // shifted/aligned divisor D'
//wire  [33:0]    p_fb;                   // P' from adder 2/3 mux (removed)
wire  [33:0]    d_fb;                   // D' from shifter
wire  [33:0]    shifter_din;            // mux data to shifter
wire   [5:0]    shifter_count;          // E or 1

// controls for adder path

/// wire            adder_1_sub;            // 1 = subtract, 0 = add
wire            adder_2_sub;            // 1 = subtract, 0 = add
wire            adder_3_sub;            // 1 = subtract, 0 = add
wire            cz3;                    // forms a constant for quotient
                                        // correction, function of quo_sign

wire  [33:0]    adder_1_result;
wire  [34:0]    adder_2_result;
wire  [33:0]    adder_3_result;

wire  [33:0]    adder_1_op1;
wire  [35:0]    adder_2_op1;
wire  [35:0]    adder_3_op1;

reg   [33:0]    adder_1_op2;
wire  [35:0]    adder_2_op2;
wire  [35:0]    adder_3_op2;

wire  [35:0]    adder_3_op3;

wire            radix4_ct_done;

wire            p_eq_minus_abs_d;       // compare of final remainder for
                                        //                the correction step
reg             p_eq_minus_abs_d_r;     // registered version
wire            p_eq_zero;
wire            divf_res_zero;

wire  [33:0]    q;            // Quotient holding register, positive - shared
                              // with staging register for mul/div result
wire  [33:0]    qn;           // Quotient holding register, negative - shared
                              // with multiplier result datapath
reg   [33:0]    q_pre;
wire  [33:0]    qn_pre;

wire            qi,  q0;      // intermediate radix-2 q's - positive values
wire            qin, q0n;     // intermediate radix-2 q's - negative values
wire            div_step_sub; // an alias for readability
wire            sel_4p_3d;    // an alias for readability

// Definitions for the divider sequencer state machine
//

localparam FD_STATE_IDLE        = 4'b0000;
localparam FD_STATE_DIVF_OVF    = 4'b1111;
localparam FD_STATE_ALIGN_D     = 4'b0001;
localparam FD_STATE_ALIGN_D_EQ  = 4'b1001;
localparam FD_STATE_RADIX4      = 4'b0010;
localparam FD_STATE_RADIX2      = 4'b0011;
localparam FD_STATE_LAST_RADIX4 = 4'b0110;
localparam FD_STATE_CORRECT     = 4'b0100;
localparam FD_STATE_CORRECT_EQ  = 4'b1100;
localparam FD_STATE_SHIFT_REM   = 4'b0101;
localparam FD_STATE_HOLD_WB     = 4'b0111;

// Definitions for the divider pipeline state machine
//

localparam PT_STATE_IDLE        = 3'b000;   // Possibly MP1
localparam PT_STATE_X2          = 3'b100;   // MP2
localparam PT_STATE_X3          = 3'b101;   // MP3/CA
localparam PT_STATE_HOLD_RETIRE = 3'b110;   // MP5: post-commit, result not done
localparam PT_STATE_RETIRE      = 3'b011;   // MP5: post-commit, result done

///// Pipe Tracking state-machine ////////////////////////////////////////////
//
reg   [2:0]     pt_state;             // state register: pipe tracking
reg             start_divide;         // start a divide - valid at X2, reg

reg   [2:0]     nxt_pt_state; 
reg             nxt_flush_div;
reg             nxt_pt_clear;
reg             nxt_start_divide;
reg             nxt_div_retire_req;
reg             nxt_div_busy;


///// Fast Divide sequencer //////////////////////////////////////////////////
//
reg   [3:0]     fd_state;             // registers state: fast divide sequencer
reg   [3:0]     nxt_fd_state;         // registers state

reg             divf_ovf_r;           // flag bit to hold ovf result
reg             do_radix4;            // 1 = sel 2P, 0 = sel P  (for remainder
                                      //    correction P+cZ*D)
reg             do_radix2;            // 1 = sel 2P, 0 = sel 4P
reg             correct_quo;          // correction state: load to result reg
reg             correct_rem;          // correction state: 1 = correction step
                                      //    for remainder, 0 = divide step
reg             shift_rem;            // control from sm: shift final remainder
reg             fd_state_shift_d;     // initial alignment
reg             fd_state_divf_ovf;    // verify |b|<|c| so result is fraction
reg             fd_run;               // new signal from fd_sm: enable P/D regs
reg             fd_done;              // new signal from fd_sm: result ready   
                
reg             nxt_divf_ovf;
reg             nxt_do_radix4;
reg             nxt_do_radix2;
reg             nxt_correct_quo;          
reg             nxt_correct_rem;         
reg             nxt_shift_rem;
reg             nxt_fd_state_shift_d;     
reg             nxt_fd_state_divf_ovf;     
reg             nxt_load_counter;
reg             nxt_fd_run;
reg             nxt_fd_done;

wire            divf_ovf_pos;
wire            divf_ovf_neg;

// leda N_10P_R_C on
// leda N_10P_R_D on


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Register incoming data and instruction attributes late in X1             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @ (posedge clk or posedge rst_a)
begin: input_data_PROC
  if (rst_a == 1'b1) begin // reset may not be required begin
    x2_src0_r      <=  `npuarc_DATA_SIZE'h0;
    x2_src1_r      <=  `npuarc_DATA_SIZE'h0;
    div_is_signed  <=  1'b0;
    kind_is_div    <=  1'b0;
    kind_is_divf   <=  1'b0;
  end
  else if (x1_pass & x2_enable & x1_div_op_r & x1_cond) begin
    x2_src0_r      <=  x2_src0_nxt;
    x2_src1_r      <=  x2_src1_nxt;
    div_is_signed  <=  x1_signed_op_r;
    kind_is_div    <= ~x1_div_kind_r;
    kind_is_divf   <=  1'b0;
  end
end  // input_data_PROC




//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process defining the div/rem logic at stage mp1            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// sign/zero extend, also dynamic power reduction by gating data

assign src0_extended =  start_divide ?
                       {div_is_signed & x2_src0_r[31], x2_src0_r[31:0]} :
                        33'b0;
assign src1_extended =  start_divide ?
                       {div_is_signed & x2_src1_r[31], x2_src1_r[31:0]} :
                        33'b0;

// estimate magnitude (exponent) of final quotient

npuarc_fd_ffs_33 u_fd_ffs_33_1(
              .din         (src0_extended),    // dividend
              .pos         (src1_ffs),
              .zero_det    (src1_zero),
              .minus_1_det (src1_minus_1),
              .max_neg_det (src1_max_neg)
             );

npuarc_fd_ffs_33 u_fd_ffs_33_2(
              .din         (src1_extended),    // divisor
              .pos         (src2_ffs),
              .zero_det    (src2_zero), 
              .minus_1_det (src2_minus_1),
              .max_neg_det (src2_max_neg)
             );

// register magnitude difference of dividend and divisor plus other info

reg    [6:0]    exp_nxt;
reg             dividend_sign_nxt;
reg             quo_sign_nxt;
reg             div_divz_nxt;
reg             div_ovf_nxt;
reg             x3_div_op_re_nxt;
reg             x3_rem_op_re_nxt; 
reg             x3_divf_op_re_nxt;
reg             src1_zero_nxt;

always @*
begin: instr_src_nxt_PROC
    exp_nxt             = exp;
    dividend_sign_nxt   = dividend_sign;
    quo_sign_nxt        = quo_sign;
    div_divz_nxt        = div_divz_r;
    div_ovf_nxt         = div_ovf_r;
    x3_div_op_re_nxt    = x3_div_op_re;
    x3_rem_op_re_nxt    = x3_rem_op_re;
    x3_divf_op_re_nxt   = x3_divf_op_re;
    src1_zero_nxt       = src1_zero_r;
  if (nxt_pt_clear || nxt_flush_div)        // clear all flags when done
  begin
    exp_nxt             = 7'b0;
    dividend_sign_nxt   = 1'b0;
    quo_sign_nxt        = 1'b0;
    div_divz_nxt        = 1'b0;
    div_ovf_nxt         = 1'b0;
    x3_div_op_re_nxt    = 1'b0;
    x3_rem_op_re_nxt    = 1'b0;
    x3_divf_op_re_nxt   = 1'b0;
    src1_zero_nxt       = 1'b0;
  end
  else if (start_divide && (!x2_kill))
  begin
    // leda BTTF_D002 off
    // leda W484 off
    // LMD: possible loss of carry/borrow in add/sub
    // LJ:  extended field calculation, cannot overflow
    exp_nxt             = kind_is_divf ? 7'd31 :src1_ffs - src2_ffs + 1;
    // leda W484 on
    // leda BTTF_D002 on
                 // 7-bit subtract, can be negative.
                 // Term deviates slightly from the C version:
                 //          exp = E+1, which is precisely the shift count.
                 // The +1 corrects for the first mandatory step, so that
                 // exp[5:1] correctly represents radix-4 step count and
                 // exp[0] represents radix-2 step (i.e. I1 in C)
                 
    dividend_sign_nxt = div_is_signed & x2_src0_r[31];
    quo_sign_nxt      = div_is_signed & (~src1_zero) & (x2_src0_r[31]^x2_src1_r[31]);
                      // signs differ = negative quotient (or zero)
    div_divz_nxt      = src2_zero;
    div_ovf_nxt       = ~kind_is_divf &  div_is_signed & src1_max_neg & src2_minus_1;
    x3_div_op_re_nxt  = ~kind_is_divf &  kind_is_div;
    x3_rem_op_re_nxt  = ~kind_is_divf & ~kind_is_div;
    x3_divf_op_re_nxt =  kind_is_divf;
    src1_zero_nxt     = src1_zero;
  end
end    // instr_src_PROC

always @ (posedge clk or posedge rst_a)
begin: instr_src_PROC
  if (rst_a == 1'b1) begin
    exp             <= 7'b0;
    dividend_sign   <= 1'b0;
    quo_sign        <= 1'b0;
    div_divz_r      <= 1'b0;
    div_ovf_r       <= 1'b0;
    x3_div_op_re    <= 1'b0;
    x3_rem_op_re    <= 1'b0;
    x3_divf_op_re   <= 1'b0;
    src1_zero_r     <= 1'b0;
  end
  else if ((nxt_pt_clear || nxt_flush_div) || (start_divide && (!x2_kill))) begin
    exp             <= exp_nxt;
    dividend_sign   <= dividend_sign_nxt;
    quo_sign        <= quo_sign_nxt;
    div_divz_r      <= div_divz_nxt;
    div_ovf_r       <= div_ovf_nxt;
    x3_div_op_re    <= x3_div_op_re_nxt;
    x3_rem_op_re    <= x3_rem_op_re_nxt;
    x3_divf_op_re   <= x3_divf_op_re_nxt;
    src1_zero_r     <= src1_zero_nxt;
  end
end
// exp logic

assign res_fraction = kind_is_divf ? 1'b0 :
                                     exp[6] | (exp == 7'h0) | src1_zero_r;
                 // added src1_zero_r as simple solution for 0/-N    
                 // negative exponent: quo = 0, rem = dividend
                 // exp[] is now +1 so added the term ==
                 // The exception to this is if p_eq_minus_abs_d when -2^N/2^N,
                 // which is handled by state machine

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Computational div/rem logic for radix-2 or radix-4 and correction steps  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


always @(*)
begin:  p_pre_PROC
casez ({start_divide, sel_4p_3d, correct_rem, do_radix2, do_radix4})

  5'b1????:  p_pre = {div_is_signed & x2_src0_r[31],
                      div_is_signed & x2_src0_r[31],
                      x2_src0_r[31:0]};
// The following was modified because of leda redundant warning.
// conditions are 'one hot' and mutually exclusive, so change may affect critical path.
//  5'b?1???:  p_pre =  adder_3_result[33:0];  
//  5'b??1??:  p_pre =  adder_2_result[34:1];  
//  5'b???1?:  p_pre =  adder_2_result[33:0];  
//  5'b?0??1:  p_pre =  adder_2_result[33:0];  
  5'b01???:  p_pre =  adder_3_result[33:0];  
  5'b001??:  p_pre =  adder_2_result[34:1];  
  5'b0001?:  p_pre =  adder_2_result[33:0];  
  5'b00001:  p_pre =  adder_2_result[33:0];  
  default:   p_pre =  p;

endcase
end   // p_pre_PROC


assign d_pre = start_divide ? {div_is_signed & x2_src1_r[31],
                               div_is_signed & x2_src1_r[31],
                               x2_src1_r[31:0]}             :   // load D
               fd_state_shift_d  ?
                               d_fb                         :   // shift D'
                               d                         ;      // hold value

// Instantiate shifter with pre-mux
// It's used to left-shift divisor D for alignment with dividend N or
// right-shift final remainder P for exponent correction

assign shifter_din = shift_rem ? p[33:0] :  // final remainder (in P) is
                                            //            right-shifted by E+1
                                 d[33:0];   // initial divisor is
                                            //            left-shifted by E+1

assign shifter_count = (kind_is_divf | exp[6]) ?  6'h0 :
    // convert negative to zero, so fraction remainder is N>>0 == N
                       (exp == 7'h0) && p_eq_minus_abs_d_r ?  6'h1 :
    // this is an exception case for -2^N/2N: forcing radix2 cycle w/shift = 1 
    // divisor shifted by (E+1) for alignment with the dividend 
                       exp[5:0];  // final remainder is always shifted by E+1

// instantiate the shifter module
npuarc_fd_shift_34 u_fd_shift_34(
                      .din   (shifter_din),
                      .count (shifter_count),
                      .dir   (shift_rem),   // shift remainder right, else
                                            //  (default) shift divisor left
                      .dout  (d_fb)
                      );



// adder1:
//  calculates (P+-D) for divf overflow step: sub if same sign, add otherwise,
//  then check for overflow (result sign is same as dividend)
//  calculates (2P+-D) for radix2 q' and P-|D| for compare at correction step
//
//  do_radix4  adder_1_sub  D[33]   Function
//  ---------  -----------  -----   --------
//
//     0          -          0      corr remainder, compare P-|D|:   P + ~D
//     0          -          1      corr remainder:                  P +  D
//     1          0          -      radix2 quotient calculation:  2P + D
//     1          1          -      radix2 quotient calculation:  2P - D =
//                                         = 2P + (~D + 1) = (2P + 1) + ~D
//

assign adder_1_op1 = fd_state_divf_ovf ?  {x2_src0_r[31], x2_src0_r[31:0], ~x2_src0_r[31]^x2_src1_r[31]} :
                     do_radix4         ?  {p[32:0], div_step_sub} :
                                           p[33:0];   // radix4 steps: int radix2 q'



always @(*)
begin:  adder_1_op2_PROC
casez ({fd_state_divf_ovf, do_radix4, div_step_sub, d[33]})

  4'b1???:  adder_1_op2 = (x2_src0_r[31]^x2_src1_r[31]) ?  { x2_src1_r[31],  x2_src1_r[31:0], 1'b0} :
                                                           {~x2_src1_r[31], ~x2_src1_r[31:0], 1'b1}  ;  // sub if same sign
  4'b011?:  adder_1_op2 = ~d[33:0];
  4'b00?1:  adder_1_op2 = ~d[33:0];
  default:  adder_1_op2 =  d[33:0];

endcase
end   // adder_1_op2_PROC

wire dontuse_carry;

// spyglass disable_block STARC-2.10.6.1
// spyglass disable_block W484
// SMD: Possible loss of carry or borrow in add/sub
// SJ:  STARC-2.10.6.1 is a redundant rule with leda W484, see below
    // leda BTTF_D002 off
// leda W484 off
// LMD: possible loss of carry/borrow in add/sub
// LJ:  extended field calculation, cannot overflow
assign {dontuse_carry, adder_1_result} = adder_1_op1 + adder_1_op2;
// spyglass enable_block STARC-2.10.6.1
// spyglass enable_block W484
// leda W484 on
    // leda BTTF_D002 on


// compare logic for P-|D|
// if D is positive then adder_1_result should be -1, else should be 0;
// reason: we only added ~D if D is positive

assign p_eq_minus_abs_d = d[33] ? (adder_1_result == 34'h3ffffffff) :  // -1
                                  (adder_1_result == 34'h0) ;
assign p_eq_zero        = p[33:0] == 34'h0 ? 1'b1 : 1'b0;

// register to avoid critical path in HS

reg p_eq_minus_abs_d_nxt;

always @*
begin:  p_eq_minus_abs_d_nxt_PROC
  p_eq_minus_abs_d_nxt   = p_eq_minus_abs_d_r;
  if (start_divide)
    p_eq_minus_abs_d_nxt = 1'b0;  // guaranteed zero during ALIGN_D
  else
    p_eq_minus_abs_d_nxt = p_eq_minus_abs_d;
end

always @ (posedge clk or posedge rst_a)
begin:  p_eq_minus_abs_d_PROC
  if (rst_a == 1'b1)
    p_eq_minus_abs_d_r <= 1'b0;
  else
    p_eq_minus_abs_d_r <= p_eq_minus_abs_d_nxt;
end

// detect divf with zero dividend and non-zero divisor
assign  divf_res_zero = (x2_src0_r[31:0] == 32'h0) & (x2_src1_r[31:0] != 32'h0);

// register divf overflow

reg divf_ovf_nxt;

always @*
begin:  divf_ovf_nxt_PROC
  divf_ovf_nxt = divf_ovf_r;
  if (fd_state_divf_ovf == 1'b1)
    divf_ovf_nxt = ~divf_res_zero &
                  ((adder_1_result[33]   == x2_src0_r[31]) |  // sign not changed
                   (adder_1_result[31:0] == 32'h0));           // or result is +-1
  else begin
    if (start_divide == 1'b1)
      divf_ovf_nxt = 1'b0;
  end
end

always @ (posedge clk or posedge rst_a)
begin:  divf_ovf_PROC
  if (rst_a == 1'b1)
    divf_ovf_r <= 1'b0;
  else if ((fd_state_divf_ovf == 1'b1) || (start_divide == 1'b1))
    divf_ovf_r <= divf_ovf_nxt;
end


// adder2:
// calculates (2P+-D) for radix2 step or (4P+-D) for radix4 step
// It also calculates (P + cZ*D) at remainder correction step and (2Q"+-1) at
// quotient correction step, both shifted
//
//  corr_rem  do_rdx4 add2_sub  cz3   Function
//  -------- -------- --------  ---   --------
//
//     0        0        0       -  radix2 quotient calculation:  (2P+0)  +   D
//     0        0        1       -  radix2 quotient calculation:  (2P+1)  +  ~D
//     0        1        0       -  radix4 quotient calculation:  (4P+0)  +   D
//     0        1        1       -  radix4 quotient calculation:  (4P+1)  +  ~D
//     1        -        -       0  correction for remainder:     (2P +0) +   0
//                                                                  (quo: Q + 0)
//     1        -        0       1  correction for remainder:     (2P +0) +  2D
//                                                                  (quo: Q - 1)
//     1        -        1       1  correction for remainder:     (2P +1) + ~2D 
//                                                                  (quo: Q + 1)
//
//   corr_rem  add2_sub  cz3    Function
//   --------  --------  ---   --------
//
//     1         -        0     rem correction:  (2P +0) +   0     (quo: Q + 0)
//     1         0        1     rem correction:  (2P +1) + ~2D     (quo: Q + 1)
//     1         1        1     rem correction:  (2P +0) +  2D     (quo: Q - 1) 
//
// Notes: adder_2_sub is generated by the Q-logic for divide step and by
//        quo_sign at remainder correction step.
//        Correction step subtract result (P-D) is shifted:
//               2*(P-D) = 2P + (-2D) = 2P + [~(2D) + 1] = (2P+1) + ~2D
//        We kept (P+D) also shifted. There is no overflow, given that we have
//        a 33-bit adder.
//        This shift is corrected at the final mux.
//
//        The negative part:  4P-D = 4P + (~D+1) = (4P+1) + ~D

// Notes: Remainder correction complements the equivalent quotient correction
//        from adder 3 logic, cz3 is the exact same signal.
//        For regular radix4 step, the add/sub is derived from previous qi

assign adder_2_sub = correct_rem & (p[33] != dividend_sign) &
                                            (quo_sign == 1) ? 1 : // subtract D
                     correct_rem & (p[33] != dividend_sign) &
                                            (quo_sign == 0) ? 0 : // add D
                     correct_rem & p_eq_minus_abs_d_r       &
                                            (quo_sign == 1) ? 0 : // add D
                     correct_rem & p_eq_minus_abs_d_r       &
                                            (quo_sign == 0) ? 1 : // subtract D
// default term derived from previous qi, only applies to radix_4 divide step
                                                              div_step_sub;

assign adder_2_op1 = correct_rem ? {p[33],   p[33:0], adder_2_sub} :
                                               // remainder correction step: 2P
                     do_radix4   ? {p[33:0],    1'b0, adder_2_sub} :
                                               //              radix4 steps: 4P
                                   {p[33],   p[33:0], adder_2_sub};
                                               //              radix2 steps: 2P

assign adder_2_op2 = correct_rem & (~cz3)         ? 0                           :
                                 // during remainder correction step: 2D or ~2D
                     correct_rem &  adder_2_sub ? {~d[33], ~d[33:0],    1'b1} :
                     correct_rem & (~adder_2_sub) ? { d[33],  d[33:0],    1'b0} :
                                 // during divide steps: ~d or d
                     adder_2_sub ?                {~d[33], ~d[33],  ~d[33:0]} :
                                                  { d[33],  d[33],   d[33:0]};
                     
// leda B_3208 off
// leda BTTF_D002 off
// leda W484 off
// LMD: possible loss of carry/borrow in add/sub
// LJ:  extended field calculation, cannot overflow
// spyglass disable_block W164a
// spyglass disable_block W164b
// spyglass disable_block W484
// SMD: LHS less than RHS of assignment 
// SJ:  extended field of calculation cannot overflow
assign adder_2_result = adder_2_op1 + adder_2_op2;
// leda W484 on
// leda BTTF_D002 on
// leda B_3208 on
// spyglass enable_block W164a
// spyglass enable_block W164b
// spyglass enable_block W484


// adder3:
//  Calculates (4P+-3D) for radix4 step;
//  Also final quotient (including Q - Qn) with corrections
//
// corr_quo  add3_sub  cz3  Function
// --------  --------  ---  --------
//
//   0         0       -    radix4 quo calc: 4P + 3D = (4P+0) +  2D +  D
//   0         1       -    radix4 quo calc: 4P - 3D = (4P+2) + ~2D + ~D
//   1         -       0    quo correction:  Q - Qn + 0 = Q + (~Qn+1) + 0 =
//                                                               = Q + ~Qn + 1
//   1         0       1    quo correction:  Q - Qn + 1 = Q + (~Qn+1) + 1 =
//                                                               = Q + ~Qn + 2
//   1         1       1    quo correction:  Q - Qn - 1 = Q + (~Qn+1) + (~1+1) =
//                                                               = Q + ~Qn + 0 
//   
// Notes: adder_3_sub is generated by the Q-logic for divide step and correction
//        logic for quotient correction
//
//        This stage starts with a 3:2 CSA:  4P+3D = 4P + 2D + D
//        The negative part:  4P-3D = 4P + (~2D+1) + (~D+1) = (4P+2) + ~2D + ~D
//


// Note: for             3 options,
//       so we assigned these to {adder_3_sub,cz3}
//       For regular radix4 step, the add/sub is derived from previous qi

assign adder_3_sub = correct_quo & (p[33] != dividend_sign) & (quo_sign == 1) ?
                                                              0 :  // add 1
                     correct_quo & (p[33] != dividend_sign) & (quo_sign == 0) ?
                                                              1 :  // subtract 1
                     correct_quo & p_eq_minus_abs_d_r       & (quo_sign == 1) ?
                                                              1 :  // subtract 1
                     correct_quo & p_eq_minus_abs_d_r       & (quo_sign == 0) ?
                                                              0 :  // add 1
// default term derived from previous qi, only applies to radix_4 divide step
                     div_step_sub;          
                  
assign cz3         = ((p[33] != dividend_sign) | p_eq_minus_abs_d_r) &
                     (~p_eq_zero) & (~res_fraction);
                                   // only applies during quotient correction
                                   // last term forces 0-0+0 "correction"

assign adder_3_op1 = correct_quo ? {2'b00, q}              :      /// LEDA: added 2'b00
                                   { p[33:0],adder_3_sub, 1'b0};
                                   // radix4 steps: 4P+2
               
assign adder_3_op2 = correct_quo ?  {2'b11, ~qn}            :     /// LEDA: added 2'b11
                     adder_3_sub ? {~d[33], ~d[33:0], 1'b1} :
                                   { d[33],  d[33:0], 1'b0};
                                   // during divide steps: 2d or ~2d
                                                             
assign adder_3_op3 = correct_quo ? { 34'b0, ~adder_3_sub & cz3 , ~cz3} :
                     adder_3_sub ? {~d[33], ~d[33], ~d[33:0]}          :
                                   { d[33],  d[33],  d[33:0]};
                                   // during radix4 step: D or ~D

// The following 3-term add must be synthesized as CSA3:2 into a full-adder
// leda B_3208 off
// leda BTTF_D002 off
// leda W484 off
// LMD: possible loss of carry/borrow in add/sub
// LJ:  extended field calculation, cannot overflow
// spyglass disable_block W164a
// spyglass disable_block W164b
// spyglass disable_block W484
// SMD: LHS less than RHS in assignment
// SJ:  extended field of calculation, cannot overflow
assign adder_3_result = adder_3_op1 + adder_3_op2 + adder_3_op3;
                                   // quotient correction result is not shifted
// leda W484 on
// leda BTTF_D002 on
// leda B_3208 on
// spyglass enable_block W164a
// spyglass enable_block W164b
// spyglass enable_block W484


// Quotient logic
// The non-restoring algorithm generates positive or negative partial quotients.
// The two are accumulated separately in Q (positive) or Qn (negative).
// During correction step, the non-redundant quotient is calculated, in addition
// to the +-1 of the correction step itself, see adder 3 logic above.
// We chose this method rather than form two conditional results (with or w/o
// borrow) on the fly because we have the adder logic in place during the
// correction step, making this approach simple and low-cost.
// Note: the precise non-restoring divide uses a digit set {1,-1} for the
//       quotient bits, so potentially Qn = ~Q.
//       This would have been true for a full-size divide, but not true for the
//       sign bits (which we skip).
//       Additional sign extension information is needed, so we chose to
//       implement the simplest method and form Qn separate from Q, requiring a
//       subtract step at the end. This step is merged with quotient correction,
//       so it does not incur a clock cycle penalty. 

assign qi  = p[33] == d[33] ?              1'b1 : 1'b0; // qi from previous div
                                                   // step or from initial load
assign qin = p[33] == d[33] ?              1'b0 : 1'b1;
assign q0  = adder_1_result[33] == d[33] ? 1'b1 : 1'b0; // q0 from intermediate
                                                   // radix-2 logic (adder 1)
assign q0n = adder_1_result[33] == d[33] ? 1'b0 : 1'b1;

assign div_step_sub = qi;                          // an alias for readability
assign sel_4p_3d    = q0 == qi ? do_radix4 : 0;    // both radix-2 stages are
                           // in the same "direction" (add or subtract)

// Q and Qn logic and registers, Q is also the final result

// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
// spyglass disable_block STARC05-2.8.1.3
always @(*)
begin:   q_pre_PROC
if ((fd_state == FD_STATE_CORRECT) && p_eq_minus_abs_d)
             q_pre =  q;
else
casez ({fd_state_shift_d, correct_quo, shift_rem, do_radix2, do_radix4})

  5'b1????:  q_pre =  34'b0;
  5'b????1:  q_pre = {q[31:0], qi, q0 };  
  5'b???1?:  q_pre = {q[32:0], qi };  
  5'b?1???:  q_pre = {2'h0,adder_3_result[31:0]};  
  5'b??1??:  q_pre =  d_fb;  
  default:   q_pre =  q;

endcase
end    // q_pre_PROC

assign qn_pre = fd_state_shift_d  ?  34'b0                 :
                           // Qn is positive magnitude:
                           //      it accumulates -1 quotient bits as +1 values
                do_radix4         ?  {qn[31:0],qin,q0n}    :
                do_radix2         ?  {qn[32:0],qin}        :
                                      qn                  ;
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
// Sequential block defining the divide-stage input data registers          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin:   P_D_regs_PROC
  if (rst_a == 1'b1) begin
    p_tmp_r <= 34'd0;
    d_tmp_r <= 34'd0;
  end
  else if (start_divide || fd_run) begin // new signal from fd_sm: enable P/D regs
    p_tmp_r <= p_pre;
    d_tmp_r <= d_pre;         
  end
end  // P_D_regs_PROC

// aliases for the divide logic
assign p = p_tmp_r;
assign d = d_tmp_r;

//////////////////////////////////////////////////////////////////////////////
// Sequential blocks defining temporary and final Result pipeline registers //
//////////////////////////////////////////////////////////////////////////////

// Result reg
always @(posedge clk or posedge rst_a)
begin:   div_result_r_PROC
  if (rst_a == 1'b1) begin
    div_result_r    <= 68'd0;
  end
  else if (div_busy_r) begin
    div_result_r    <= {qn_pre,q_pre};
                                     // Q/Qn is div_result[]
                                     // must be in this order: result = Q
  end
end   // div_result_r_PROC

// aliases for the divide logic
assign qn = div_result_r[67:34];
assign q  = div_result_r[33:0] ;


//////////////////////////////////////////////////////////////////////////////
// Output drives                                                            //
//////////////////////////////////////////////////////////////////////////////

assign div_retire_overflow_r =  div_ovf_r | div_divz_r;

assign divf_ovf_pos = divf_ovf_r & ~(x2_src0_r[31]^x2_src1_r[31]);
assign divf_ovf_neg = divf_ovf_r &  (x2_src0_r[31]^x2_src1_r[31]);

always@*
begin
   if (divf_res_zero || (kind_is_divf && div_divz_r))
     div_retire_result_r = 32'h0;
   else
   if (divf_ovf_neg)
     div_retire_result_r = 32'h8000_0000;
   else
   if (divf_ovf_pos)
     div_retire_result_r = 32'h7fff_ffff;
   else
   if (div_retire_overflow_r)
     div_retire_result_r = 32'h0;
   else
     div_retire_result_r = div_result_r[31:0];
end

assign div_retire_sign_r     = (div_is_signed &  div_result_r[31] &
                                (~div_retire_overflow_r) & (~divf_ovf_r) & (~divf_res_zero)) |
                               (divf_ovf_neg & (~div_divz_r));

assign div_retire_zero_r     = (div_result_r[31:0] == 32'd0) &
                               (~div_retire_overflow_r) & (~divf_ovf_r) |
                               ((~div_retire_overflow_r) & divf_res_zero);


//==============  Fast Divider State Machine Logic  ==========================

//
// Notes: exception handling in the divide module
//   The div-by-zero condition is detected early and exception signal raised.
//   This module does not know if exception is enabled, so the handshake is
//   very critical.
//   If divz exception is enabled, pipeline will immediately signal with a
//   _restart and the state_machine will go to idle, otherwise it will proceed
//   to the write-back stage and updates flags, on the assumption that
//   exception is disabled.
//   This behavior is specific to the 3-stage pipeline control and may need
//   to change for another design.
//

// State Registers: fast divide sequencer

reg [3:0] fd_state_nxt;
wire[3:0] fd_state_next;
reg       fd_run_nxt;           
reg       fd_done_nxt;           
reg       do_radix4_nxt;
reg       do_radix2_nxt;
reg       correct_quo_nxt;
reg       correct_rem_nxt;
reg       shift_rem_nxt;
reg       fd_state_shift_d_nxt;             
reg       fd_state_divf_ovf_nxt;   

always @*
begin:   fd_state_nxt_PROC
  fd_state_nxt               =  fd_state;
  fd_run_nxt                 =  fd_run;
  fd_done_nxt                =  fd_done;
  do_radix4_nxt              =  do_radix4;
  do_radix2_nxt              =  do_radix2;
  correct_quo_nxt            =  correct_quo;
  correct_rem_nxt            =  correct_rem;
  shift_rem_nxt              =  shift_rem;
  fd_state_shift_d_nxt       =  fd_state_shift_d;             
  fd_state_divf_ovf_nxt      =  fd_state_divf_ovf;      
  if (nxt_pt_clear || nxt_flush_div)
  begin
    fd_state_nxt               =  FD_STATE_IDLE;
    fd_run_nxt                 =  1'b0;
    fd_done_nxt                =  1'b0;
    do_radix4_nxt              =  1'b0;
    do_radix2_nxt              =  1'b0;
    correct_quo_nxt            =  1'b0;
    correct_rem_nxt            =  1'b0;
    shift_rem_nxt              =  1'b0;
    fd_state_shift_d_nxt       =  1'b0;             
    fd_state_divf_ovf_nxt      =  1'b0;     
  end
  else
  begin
    fd_state_nxt               =  nxt_fd_state;              
    fd_run_nxt                 =  nxt_fd_run;           
    fd_done_nxt                =  nxt_fd_done;           
    do_radix4_nxt              =  nxt_do_radix4;
    do_radix2_nxt              =  nxt_do_radix2;
    correct_quo_nxt            =  nxt_correct_quo;             
    correct_rem_nxt            =  nxt_correct_rem;             
    shift_rem_nxt              =  nxt_shift_rem;             
    fd_state_shift_d_nxt       =  nxt_fd_state_shift_d;      
    fd_state_divf_ovf_nxt      =  nxt_fd_state_divf_ovf;    
  end
end   // fd_state_PROC

assign fd_state_next =
                        fd_state_nxt;

always @ (posedge clk or posedge rst_a)
begin:   fd_state_PROC
  if (rst_a == 1'b1) begin
    fd_state               <=  FD_STATE_IDLE;
    fd_run                 <=  1'b0;           
    fd_done                <=  1'b0;           
    do_radix4              <=  1'b0;
    do_radix2              <=  1'b0;
    correct_quo            <=  1'b0;
    correct_rem            <=  1'b0;
    shift_rem              <=  1'b0;
    fd_state_shift_d       <=  1'b0;             
    fd_state_divf_ovf      <=  1'b0;      
  end
  else begin
    fd_state               <=  fd_state_next;              
    fd_run                 <=  fd_run_nxt;           
    fd_done                <=  fd_done_nxt;           
    do_radix4              <=  do_radix4_nxt;
    do_radix2              <=  do_radix2_nxt;
    correct_quo            <=  correct_quo_nxt;             
    correct_rem            <=  correct_rem_nxt;             
    shift_rem              <=  shift_rem_nxt;             
    fd_state_shift_d       <=  fd_state_shift_d_nxt;      
    fd_state_divf_ovf      <=  fd_state_divf_ovf_nxt; 


  end
end

// State Logic

always @ (*)
begin: fast_divider_state_transitions_PROC

    // defaults
    nxt_fd_state            =   FD_STATE_IDLE;        
    nxt_do_radix4           =   1'b0;
    nxt_do_radix2           =   1'b0;
    nxt_correct_quo         =   1'b0;            
    nxt_correct_rem         =   1'b0;            
    nxt_shift_rem           =   1'b0;
    nxt_fd_state_shift_d    =   1'b0;     
    nxt_fd_state_divf_ovf   =   1'b0;     
    nxt_load_counter        =   1'b0;
    nxt_fd_run              =   1'b0;
    nxt_fd_done             =   1'b0;


case (fd_state)


 FD_STATE_IDLE:  
 begin
   if (start_divide & kind_is_divf)              // X2 status from pt_state
     begin
       nxt_fd_state         =  FD_STATE_DIVF_OVF;                   
       nxt_fd_state_divf_ovf=  1'b1;             // check fractional overflow 
     end
   else
   if (start_divide)                             // not divf
     begin
       nxt_fd_state         =  FD_STATE_ALIGN_D;                   
       nxt_fd_state_shift_d =  1'b1;             // initialize Q,Qn next clock 
       nxt_fd_run           =  1'b1;
     end
   else
     begin
       nxt_fd_state         =  FD_STATE_IDLE;                   
     end  
 end


 FD_STATE_DIVF_OVF:  
 begin
   if (divf_res_zero)                            // 0/N
     begin
       nxt_fd_state         =  FD_STATE_HOLD_WB;
       nxt_fd_done          =  1'b1;
     end
   else
     begin
       nxt_fd_state         =  FD_STATE_ALIGN_D;                   
       nxt_fd_state_shift_d =  1'b1;             // initialize Q,Qn next clock 
       nxt_fd_run           =  1'b1;
     end
 end


 FD_STATE_ALIGN_D:                               // X3
 begin
   nxt_fd_run               =  1'b1;
   if (divf_ovf_r)                               // divf overflow, skip divide  
     begin
       nxt_fd_state         =  FD_STATE_CORRECT; // we need one clock to mux
                                                 // the results, so go to _corr
     end                                          
   else
   if (res_fraction && p_eq_minus_abs_d)         // needs to run one step,
                                                 //      corner case -2^N/2^N  
     begin
       nxt_fd_state         =  FD_STATE_ALIGN_D_EQ;
                                                 // split critical path
                                                 // shifter_count == 0, so no
                                                 // change to source operands
       nxt_fd_state_shift_d =  1'b1;             // initialize Q,Qn next clock 
     end
   else
   if (res_fraction || div_divz_r || div_ovf_r)  // no divide steps: result is
                                                 // known from decoding operands  
     begin                                       // exp<0: fraction, D=0 (divz),
                                                 // signed 0x8000_0000/-1
       nxt_fd_state         =  FD_STATE_CORRECT; // we need one clock to mux
                                                 // the results, so go to _corr
       nxt_correct_quo      =  x3_div_op_re;
       nxt_correct_rem      =  x3_rem_op_re;
     end                                          
   else
   if (do_radix4_steps)
     begin
       nxt_fd_state         =  FD_STATE_RADIX4;             
       nxt_load_counter     =  1'b1;            // this signal is used raw, no
                                                //          time to register it
       nxt_do_radix4        =  1'b1;
     end
   else
     begin
       nxt_fd_state         =  FD_STATE_RADIX2; // exp == 0, only radix 2 step
                                                //                    required
       nxt_do_radix2        =  1'b1;
     end
 end                                           // we need one clock to mux the
                                               // results, so go to _corr

 FD_STATE_ALIGN_D_EQ:   // shift by 1 after (exp == 0) && p_eq_minus_abs_d
     begin
       nxt_fd_state         =  FD_STATE_RADIX2;
       nxt_do_radix2        =  1'b1;
       nxt_fd_run           =  1'b1;
     end


 FD_STATE_RADIX4:
 begin
   nxt_fd_run               =  1'b1;
   if (radix4_ct_done &&  do_radix2_step)
     begin
       nxt_fd_state         =  FD_STATE_RADIX2;  // radix 2 step required
       nxt_do_radix2        =  1'b1;
     end
   else
   if (radix4_ct_done && (!do_radix2_step))
     begin
       nxt_fd_state         =  FD_STATE_CORRECT; // done with divide steps,
                                                 //        proceed to _corr
       
       nxt_correct_quo      =  x3_div_op_re | x3_divf_op_re;
       nxt_correct_rem      =  x3_rem_op_re;
     end
   else
     begin
       nxt_fd_state         =  FD_STATE_RADIX4;  // not done with radix 4
                                                 //                  steps
       nxt_do_radix4        =  1'b1;
     end
 end


 FD_STATE_RADIX2:
 begin
       nxt_fd_state          =  FD_STATE_CORRECT;  // only one radix 2 divide
                                                   //   step, proceed to _corr
       nxt_correct_quo       =  x3_div_op_re | x3_divf_op_re;
       nxt_correct_rem       =  x3_rem_op_re;
       nxt_fd_run            =  1'b1;
 end



 FD_STATE_CORRECT:
 
 // Arriving to this state after divide steps or direct from shift_d
 // Note that a divz overflow exception flag is generated earlier but the EXU
 // control can only abort with a wa_restart if taken. The wa_restart would
 // be qualified as a nxt_pt_flush, not considered in case logic but has a
 // reset effect on the register logic of fd_state.
 // if divz or ovf conditions then no results written and no need to manipulate
 // inputs to adders, but still should generate appropriate flags.
 // if arriving with res_fraction then Q, Qn == 0 and P == N (need to suppress
 // earlier write to N!).
 // We force cz3 = 0 so then quo => 0 in correction stage.
 // Remainder is fine if we don't shift it, so we force shifter_count = 0.
 //
 // All "anomalies" and the standard correction are covered in adder source
 // selection logic, so only state transitions are covered here
 //
 
 begin
   nxt_fd_run                =  1'b1;
   if (div_divz_r || div_ovf_r || divf_ovf_r)        // no result, just flags  
   begin
     nxt_fd_state             =  FD_STATE_HOLD_WB;
     nxt_fd_done              =  1'b1;
    end                                               
   else
   if (p_eq_minus_abs_d)
   begin
     nxt_fd_state             =  FD_STATE_CORRECT_EQ;
                                                     // extension state
     nxt_correct_quo          =  x3_div_op_re | x3_divf_op_re;
     nxt_correct_rem          =  x3_rem_op_re;
   end
   else
   if (correct_quo)
   begin
     nxt_fd_state             =  FD_STATE_HOLD_WB;   // result will be in Q reg
                                                     //               next cycle
     nxt_fd_done              =  1'b1;
   end
   else
   begin
     nxt_fd_state             =  FD_STATE_SHIFT_REM; // shift remainder as
                                                     //                  needed
     nxt_shift_rem            =  1'b1;               // controls shifter
                                                     //               direction
   end
 end


FD_STATE_CORRECT_EQ:
 begin
   nxt_fd_run                 =  1'b1;
   if (correct_quo)
   begin
     nxt_fd_state             =  FD_STATE_HOLD_WB;   // result will be in Q reg
                                                     //               next cycle
     nxt_fd_done              =  1'b1;
   end
   else
   begin
     nxt_fd_state             =  FD_STATE_SHIFT_REM; // shift remainder as
                                                     //                  needed
     nxt_shift_rem            =  1'b1;               // controls shifter
                                                     //               direction
   end
 end


FD_STATE_SHIFT_REM:
 begin
   nxt_fd_state               =  FD_STATE_HOLD_WB;   // result will be in Q reg
                                                     //               next cycle                   
   nxt_fd_done                =  1'b1;
   nxt_fd_run                 =  1'b1;
 end


 FD_STATE_HOLD_WB: 
 begin
   if (start_divide)                                 // from pt_state
   begin
     nxt_fd_state             =  FD_STATE_ALIGN_D;              
     nxt_fd_state_shift_d     =  1'b1;               // init Q,Qn next clock 
     nxt_fd_run               =  1'b1;
   end
   else
   if (nxt_pt_clear)
   begin
     nxt_fd_state             =  FD_STATE_IDLE;              
   end
   else
   begin
     nxt_fd_state             =  FD_STATE_HOLD_WB;   // result is in Q reg                   
     nxt_fd_done              =  1'b1;               //   or no result if ovf
     nxt_fd_run               =  1'b1;
   end
 end


 default:  
 begin
   begin
     nxt_fd_state             =  FD_STATE_IDLE;                   
   end  
 end

endcase
end      // fast_divider_state_transitions_PROC

  // concept: 2-bit q vector is pipelined. 1-bit is available from last divide
  // step and 1 bit is calculated on-the-fly during the radix-4 divide step.
  // Because of this, we must execute at least one divide step for exp >= 0.
  //      exp     radix-2 steps     radix-4 steps
  //      ---     -------------     -------------
  //      <0  <=0       0                 0
  //       0    1       1                 0
  //       1    2       0                 1  <- correction required for count,
  //                                                                  shift is 0
  //       2    3       1                 1
  //       3    4       0                 2
  //       4    5       1                 2
  //       5    6       0                 3
  //      ...
  //    

// always load exp[5:1] to counter but skip states based on registered exp[6:0]
// we always go to state SHIFT_D, no optimization done for the skip cases
assign do_radix4_steps = ~exp[6] & (exp[5:1] != 5'b0);
                              // none-negative (guaranteed fraction if negative)
assign do_radix2_step  = ~exp[6] &  exp[0];
                              // non-negative even count (exp is count+1)


// instantiate down counter, used by the state machine to count radix4 steps

npuarc_fd_radix4_counter u_fd_radix4_counter(
                    .clk     (clk),
                    .reset_a (rst_a),
                    .start   (nxt_load_counter), // issued by state machine:
                                                 //          shift_d -> radix_4
                    .hold    (1'b0),
                    .init_ct (exp[6:1]),
                    .done    (radix4_ct_done)
                   );




//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline Tracking logic                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Combinational logic from exu state signals

assign div_in_x1        = x1_pass & x2_enable & x1_div_op_r & x1_cond;
                          
assign div_is_commiting = ca_div_op_r & ca_commit & ca_predicate_r;

assign div_grad_req     = ca_div_op_r;          // asynchronous, speculative

assign div_unit_enable  = sa_div_op_r | x1_div_op_r | div_busy_r;

// State Registers: pipeline tracking logic
reg                       div_ret_pend_r;

reg [2:0] pt_state_nxt;
wire[2:0] pt_state_next;
reg start_divide_nxt;
reg div_retire_req_nxt;
reg div_ret_pend_nxt;
reg div_busy_nxt;
reg [`npuarc_GRAD_TAG_RANGE] div_retire_tag_nxt;

always @ *
begin:   pt_state_nxt_PROC
    pt_state_nxt              =  pt_state;
    start_divide_nxt          =  start_divide;           // to fd_state logic
    div_retire_req_nxt        =  div_retire_req_r;
    div_ret_pend_nxt          =  div_ret_pend_r;
    div_busy_nxt              =  div_busy_r;           // to exu
    div_retire_tag_nxt        =  div_retire_tag_r;
  if (nxt_pt_clear || nxt_flush_div)         // clear state when done
  begin
    pt_state_nxt              =  PT_STATE_IDLE;
    start_divide_nxt          =  1'b0;           // to fd_state logic
    div_retire_req_nxt        =  1'b0;
    div_ret_pend_nxt          =  1'b0;
    div_busy_nxt              =  1'b0;           // to exu
    div_retire_tag_nxt        =  `npuarc_GRAD_TAG_BITS'h0;
  end
  else begin
    pt_state_nxt              =  nxt_pt_state;              
    start_divide_nxt          =  nxt_start_divide;
    div_retire_req_nxt        =  nxt_div_retire_req;
    div_ret_pend_nxt          =  div_grad_req  & ca_div_grad_ack;
    div_busy_nxt              =  nxt_div_busy;
    if (div_grad_req  & ca_div_grad_ack)        // tag is assigned
      div_retire_tag_nxt      =  ca_div_grad_tag;
  end
end   // pt_state_PROC

assign pt_state_next =
                        pt_state_nxt;

always @ (posedge clk or posedge rst_a)
begin:   pt_state_PROC
  if (rst_a == 1'b1) begin
    pt_state                <=  PT_STATE_IDLE;
    start_divide            <=  1'b0;           // to fd_state logic
    div_retire_req_r        <=  1'b0;
    div_ret_pend_r          <=  1'b0;
    div_busy_r              <=  1'b0;           // to exu
  end
  else begin
    pt_state                <=  pt_state_next;              
    start_divide            <=  start_divide_nxt;
    div_retire_req_r        <=  div_retire_req_nxt;
    div_ret_pend_r          <=  div_ret_pend_nxt;
    div_busy_r              <=  div_busy_nxt;
  end
end   // pt_state_PROC

always @ (posedge clk or posedge rst_a)
begin:   div_retire_tag_PROC
  if (rst_a == 1'b1)
    div_retire_tag_r        <=  `npuarc_GRAD_TAG_BITS'h0;
  else if (nxt_pt_clear || nxt_flush_div || (div_grad_req  & ca_div_grad_ack))
    div_retire_tag_r        <=  div_retire_tag_nxt;
end

// State Logic: pipe tracking logic

always @ (*)
begin: pipeline_tracking_state_transitions_PROC

  // defaults
  nxt_pt_state            =  pt_state;     
  nxt_flush_div           =  1'b0;
  nxt_pt_clear            =  1'b0; 
  nxt_start_divide        =  1'b0;
  nxt_div_retire_req      =  1'b0;
  nxt_div_busy            =  1'b0;

  case (pt_state)

  PT_STATE_IDLE:
  // idle state is synchronized with the idle state of the divide sequencer 
  if (div_in_x1)                                // new divide instruction
    begin
    nxt_pt_state          =  PT_STATE_X2;                   
    nxt_start_divide      =  1'b1;              // start div/rem instruction 
    nxt_div_busy          =  1'b1;
    end
  else
    begin
    nxt_pt_state          =  PT_STATE_IDLE;                   
    end

  PT_STATE_X2:
  // this is the divider's X2 stage
  if (x2_kill)
    begin
    nxt_pt_state          =  PT_STATE_IDLE;                   
    nxt_flush_div         =  1'b1;
    end
  else
    begin
    nxt_pt_state          =  PT_STATE_X3;             
    nxt_div_busy          =  1'b1;
    end

  PT_STATE_X3:
  // This is divider's third cycle, corresponding to a DIV,REM instruction
  // that could be anywhere in the {X2, X3, CA} stages.
  // Divider holds in this state until it's promoted past the EXU commit stage.
  // This protocol is only for synchronization with EXU pipeline; the divider
  // will exit this state when it is committed by the EXU logic.
  // If the divide result is reached earlier than a commit, the FD logic would
  // hold the fd_done and so the PT state does not need to change.
  // There can be at most one DIV, REM instruction in X2, X3 or CA, so any
  // killed stage for which the div_op ucode but is set means that the
  // current DIV/REM instruction has been killed.
  //
  if (   (x2_kill & x2_div_op_r) 
        | (x3_kill & x3_div_op_r)
        | (ca_kill & ca_div_op_r)
      )
      begin
      nxt_pt_state        =  PT_STATE_IDLE;                   
      nxt_flush_div       =  1'b1;
      end
   else
     begin
     nxt_div_busy         =  1'b1;
     casez ({div_is_commiting, fd_done})

      2'b0?: nxt_pt_state =  PT_STATE_X3;
      2'b10: begin
             if (div_grad_req && !ca_div_grad_ack)
             begin
               nxt_pt_state       =  PT_STATE_IDLE;
               nxt_div_busy       =  1'b0;
               nxt_div_retire_req =  1'b0;
               nxt_flush_div      =  1'b0;
             end
             else begin
               nxt_pt_state =  PT_STATE_HOLD_RETIRE;
             end
             end
      2'b11: begin
             if (div_grad_req && !ca_div_grad_ack)
             begin
               nxt_pt_state       =  PT_STATE_IDLE;
               nxt_div_busy       =  1'b0;
               nxt_div_retire_req =  1'b0;
               nxt_flush_div      =  1'b0;
             end
             else begin
               nxt_pt_state       =  PT_STATE_RETIRE;
               nxt_div_retire_req =  1'b1;
             end
             end

     endcase
     end
 
  PT_STATE_HOLD_RETIRE:
  // similar to retire state, except that results are not ready
  // this state is the most likely for the divider, since exu is expected to
  // pre-commit the div/rem and assign graduation buffer tag before it is done
  begin
   nxt_div_busy           =  1'b1;
   if (fd_done)                                 // results became ready
     begin
     nxt_pt_state         =  PT_STATE_RETIRE;  
     nxt_div_retire_req   =  1'b1;
     end
  end


  PT_STATE_RETIRE:
  // divide is done and tag was assigned
  // issue retire request and wait for ack
  begin
   nxt_div_busy           =  1'b1;
   if (ca_div_retire_ack)
     begin
     nxt_pt_state         =  PT_STATE_IDLE;   
     nxt_pt_clear         =  1'b1; 
     end
   else
     begin
     nxt_pt_state         =  PT_STATE_RETIRE; 
     nxt_div_retire_req   =  1'b1;
    end
  end

  default:  
    begin
    nxt_pt_state           =  PT_STATE_IDLE;                   
    nxt_pt_clear           =  1'b1; 
    end

  endcase
end      // pipeline_tracking_state_transitions_PROC


endmodule

