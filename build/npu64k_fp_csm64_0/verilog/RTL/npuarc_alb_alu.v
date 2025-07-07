// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//    #     #        #     #
//   # #    #        #     #
//  #   #   #        #     #
// #     #  #        #     #
// #######  #        #     #
// #     #  #        #     #
// #     #  #######   #####
//
// ===========================================================================
//
// Description:
//
//  The ALU module implements the base-case arithmetic and logical operators,
//  and the proprietary single-cycle extensions, for the Albacore processor.
//
//  This module constains no state elements.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"
`include "npuarc_decode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_alu (

  ////////// Input values for the ALU operation //////////////////////////////
  //
  input   [`npuarc_DATA_RANGE]     alu_src1,           // ALU source operand 1
  input   [`npuarc_DATA_RANGE]     alu_src2,           // ALU source operand 2
  input                     carry_in,           // carry flag input
  input   [`npuarc_DATA_RANGE]     x1_link_addr_r,     // link address from BL/JL

  ////////// Microcode control signals for the ALU ///////////////////////////
  //
  input                     x1_add_op_r,
  input                     x1_mov_op_r,
  input                     x1_or_op_r,
  input                     x1_and_op_r,
  input                     x1_xor_op_r,

  input                     x1_min_op_r,
  input                     x1_max_op_r,
  input                     x1_abs_op_r,

  input                     x1_simple_shift_op_r,
  input                     x1_barrel_shift_op_r,
  input                     x1_with_carry_r,
  input                     x1_force_cin_r,
  input                     x1_inv_src1_r,
  input                     x1_inv_src2_r,
  input                     x1_bit_op_r,
  input                     x1_mask_op_r,
  input                     x1_src2_mask_sel_r,
  input                     x1_signed_op_r,
  input                     x1_half_size_r,
  input                     x1_byte_size_r,
  input                     x1_left_shift_r,
  input                     x1_rotate_op_r,
  input                     x1_src2_sh1_r,
  input                     x1_src2_sh2_r,
  input                     x1_src2_sh3_r,
  input                     x1_norm_op_r,
  input                     x1_swap_op_r,
  input                     x1_setcc_op_r,
  input                     x1_link_r,
  input                     x1_dslot_r,
  input [2:0]               x1_cc_field_r,
  
  ////////// Result outputs from the ALU operation ///////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]  alu_shift_src2,     // optionally-shifted src2
  output     [`npuarc_DATA_RANGE]  alu_sum_no_cin,     // src1+src2 with no carry-in
  output reg [`npuarc_DATA_RANGE]  alu_result,         // result from ALU operation
  output reg                alu_z_out,          // Zero result from ALU
  output reg                alu_n_out,          // Negative result from ALU
  output reg                alu_c_out,          // Carry result from ALU
  output reg                alu_v_out,          // oVerflow result from ALU
  output                    adder_lessthan,     // A < B condition from adder
  output reg                alu_brcc_cond      // BRcc outcome

);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Wires and regs for local non-registered signals                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg   [`npuarc_DATA_RANGE]         opt_invert_src1;    // optionally-inverted src1
reg   [`npuarc_DATA_RANGE]         opt_invert_src2;    // optionally-inverted src2
reg                         no_src2_shift;      // src2 doesn't shift
reg   [`npuarc_DATA_RANGE]         adder_src2;         // poss. shifted and inv'd
reg                         adder_carry_in;     // carry into adder
//reg                         nc1;                // unused carry-out
reg                         x1_logic_op;        // any logical operation
reg                         x1_min_max_op;      // either MIN or MAX operation
reg                         x1_xbfu_op;         // xbfu operation
reg                         select_ll_mux;      // need link_addr or logical op
reg                         select_adder;       // need adder output as result
reg   [`npuarc_DATA_RANGE]         link_or_logic;      // link address or logic result
reg                         setcc_result;       // result of a SETcc instr.

// Maskgen module output connections
//
wire  [`npuarc_DATA_RANGE]         x1_bit_mask;        // mask produced by maskgen
reg   [4:0]                 mask_src;           // Bit Mask

// Adder unit output connections
//
wire  [`npuarc_DATA_RANGE]         x1_adder_val;       // adder result
wire                        adder_zero;         // Z flag from adder
wire                        adder_negative;     // N flag from adder
wire                        adder_carry_out;    // C flag from adder
wire                        adder_overflow;     // V flag from adder
// Logic unit output connections
//
wire  [`npuarc_DATA_RANGE]         x1_logic_val;       // logic unit result
wire                        logic_zero;         // Z flag from logic unit
wire                        logic_negative;     // N flag from logic unit
wire                        logic_carry;        // C flag from logic unit
wire                        logic_overflow;     // V flag from logic unit

// Barrel-shift unit output connections
//
wire  [`npuarc_DATA_RANGE]         barrel_result;      // shifter result
wire                        barrel_zero;        // Z flag from shifter
wire                        barrel_negative;    // N flag from shifter
wire                        barrel_cout;        // C flag from shifter
wire                        barrel_overflow;    // V flag from shifter

// Byte manipulation unit output connection
//
wire  [`npuarc_DATA_RANGE]         swap_result;        // result from swap logic

// Bit-scan unit output connection
//
wire                        bitscan_zero;       // Z result from bitscan
wire                        bitscan_negative;   // N result from bitscan
wire  [4:0]                 bitscan_result;     // bitscan result value

// BRcc condition-decode signals, defined one-hot to optimize timing
//
reg                         eq_test;            // BREQ or SETEQ condition
reg                         lt_test;            // BRLT or SETLT condition
reg                         lo_test;            // BRLO or SETLO condition
reg                         brcc_cond;          // pre-inversion BRcc result
reg                         bbit_select;        // pre-gating BBITn result
reg                         bbit_result;        // gated BBITn result

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to select and optionally-invert source operands     //
// as required by either the adder or the logic unit.                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : alu_opd_sel_PROC

  // Optionally invert alu_src1 for use in the Adder and Logic unit for
  // RSUB, NOT and MAX instructions.
  //
  opt_invert_src1   = alu_src1 ^ {32{x1_inv_src1_r}};

  // Optionally invert alu_src2, before any application of scaling shifts,
  // for use in the Logic unit by BIC and BCLR instructions.
  //
  opt_invert_src2   = alu_src2 ^ {32{x1_inv_src2_r}};

  // Assert no_src2_shift when none of the shift inputs is enabled
  // for the ADD1, ADD2, ADD3, SUB1, SUB2 and SUB3 instructions.
  //
  no_src2_shift     = ~(x1_src2_sh1_r | x1_src2_sh2_r | x1_src2_sh3_r);

  // Create derivative of src2, optionally shifted by 1, 2 or 3 bits..
  //
  alu_shift_src2    = (  alu_src2                & {32{no_src2_shift}} )
                    | ( {alu_src2[30:0],   1'b0} & {32{x1_src2_sh1_r}} )
                    | ( {alu_src2[29:0],  2'b00} & {32{x1_src2_sh2_r}} )
                    | ( {alu_src2[28:0], 3'b000} & {32{x1_src2_sh3_r}} )
                    ;

  // Optionally invert the possibly-scaled source2 operand. This is required
  // by the SUB1, SUB2 and SUB3 instructions.
  //
  adder_src2        = alu_shift_src2 ^ {32{x1_inv_src2_r}};
                
  // Generate the adder's carry input.
  //
  adder_carry_in    = ((carry_in & x1_with_carry_r) ^ x1_inv_src2_r)
                    | x1_force_cin_r
                    ;

  // XBFU Op == (shift Op && Mask Op)
  // XBFU Op Mask == Operand  [9:5] instead of Operand [4:0]
  //
  x1_xbfu_op        = (x1_barrel_shift_op_r & x1_mask_op_r);

  mask_src          = (x1_xbfu_op == 1'b1)
                    ? alu_src2 [9:5]
                    : alu_src2 [4:0]
                    ;
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the mask generator                                           //
//                                                                          //
//  maskgen   : creates a bit mask and one-hot decoder for src2             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_maskgen u0_alb_x1_maskgen (
  .src2_val           (mask_src[4:0]        ),   // register or literal operand
  .bit_op             (x1_bit_op_r          ),   // ucode
  .mask_op            (x1_mask_op_r         ),   // ucode
  .inv_mask           (x1_inv_src2_r        ),   // ucode
  .mask_result        (x1_bit_mask          )    // result from mask generator
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate a fast integer adder unit                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_adder u_alb_x1_adder (
  .src1               (opt_invert_src1      ),
  .src2               (adder_src2           ),
  .carry_in           (adder_carry_in       ),
  .sum                (x1_adder_val         ),
  .sum_no_carry       (alu_sum_no_cin       ),
  .zero               (adder_zero           ),
  .negative           (adder_negative       ),
  .carry_out          (adder_carry_out      ),
  .overflow           (adder_overflow       ),
  .lessthan           (adder_lessthan       )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the logical unit                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_logic_unit u_alb_x1_logic_unit (
  .src1               (opt_invert_src1      ),
  .src2               (opt_invert_src2      ),
  .src2_mask          (x1_bit_mask          ),
  .carry_flag         (carry_in             ),
  .or_op              (x1_or_op_r           ),
  .and_op             (x1_and_op_r          ),
  .xor_op             (x1_xor_op_r          ),
  .mov_op             (x1_mov_op_r          ),
  .signed_op          (x1_signed_op_r       ),
  .mask_sel           (x1_src2_mask_sel_r   ),
  .byte_size          (x1_byte_size_r       ),
  .half_size          (x1_half_size_r       ),
  .shift_op           (x1_simple_shift_op_r ),
  .left               (x1_left_shift_r      ),
  .rotate             (x1_rotate_op_r       ),
  .with_carry         (x1_with_carry_r      ),
  .result             (x1_logic_val         ),
  .zero               (logic_zero           ),
  .negative           (logic_negative       ),
  .carry              (logic_carry          ),
  .overflow           (logic_overflow       )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the barrel shifter unit                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_shifter u_alb_x1_barrel_shift (
  .src1               (alu_src1           ),
  .src2_s5            (alu_src2[4:0]      ),
  .arith              (x1_signed_op_r       ),
  .left               (x1_left_shift_r      ),
  .rotate             (x1_rotate_op_r       ),
  .xbfu_op            (x1_xbfu_op           ),
  .bit_mask           (x1_bit_mask          ),
  .result             (barrel_result        ),
  .zero               (barrel_zero          ),
  .negative           (barrel_negative      ),
  .carry_out          (barrel_cout          ),
  .overflow           (barrel_overflow      )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the byte manipulation unit                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_byte_unit u_alb_x1_byte_unit (
  .swap_op            (x1_swap_op_r         ),
  .signed_op          (x1_signed_op_r       ),
  .half_size          (x1_half_size_r       ),
  .byte_size          (x1_byte_size_r       ),
  .left               (x1_left_shift_r      ),
  .rotate             (x1_rotate_op_r       ),
  .src                (alu_src2           ),
  .result             (swap_result          )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the bit-scanning unit                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_bitscan u_alb_x1_bitscan (
  .norm_op            (x1_norm_op_r         ),
  .src2_val           (alu_src2           ),
  .signed_op          (x1_signed_op_r       ),
  .half_size          (x1_half_size_r       ),
  .byte_size          (x1_byte_size_r       ),
  .zero               (bitscan_zero         ),
  .negative           (bitscan_negative     ),
  .scan_result        (bitscan_result       )
);



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for selecting the ALU result value                  //
//                                                                          //
// Form the ALU result by multiplexing the results from each of the units   //
// within the ALU.                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : alu_select_PROC

  //==========================================================================
  // Select the logic unit output as the ALU result if any one of the
  // logical operations is being performed. The MOV instruction is classed
  // as a logical operation, as the logic_unit simply passes alu_src2 to its
  // output when da_mov_op is asserted.
  //
  x1_logic_op   =  x1_mov_op_r
                |  x1_or_op_r
                |  x1_and_op_r
                |  x1_xor_op_r
                |  x1_simple_shift_op_r
                ;

  //==========================================================================
  // Select the combined result from the logic_unit and the x1_link_addr_r
  // value when either x1_logic_op, x1_link_r or x1_dslot_r are asserted.
  // If x1_logic_op is asserted, the flag outputs will come from the logic unit.
  //
  select_ll_mux = x1_link_r 
                | x1_dslot_r
                | x1_logic_op
                ;

  link_or_logic = (x1_link_r | x1_dslot_r)
                ? x1_link_addr_r
                : x1_logic_val
                ;
                
  //==========================================================================
  // Select the adder result when x1_add_op_r is asserted, but not if 
  // either x1_link_r or x1_setcc_op are also asserted.
  //
  select_adder  = x1_add_op_r
                & (~x1_link_r)
                & (~x1_dslot_r)
                & (~x1_setcc_op_r)
                ;

  //==========================================================================
  // Select the result from one of the ALU functional units.
  // The control vector is one-hot, allowing the use of casez.
  //
  casez ({ select_adder
          ,select_ll_mux
          ,x1_barrel_shift_op_r
          ,x1_swap_op_r
          ,x1_norm_op_r
          ,x1_setcc_op_r
        })
    6'b1?????:   alu_result  = x1_adder_val;
    6'b01????:   alu_result  = link_or_logic;
    6'b001???:   alu_result  = barrel_result;
    6'b0001??:   alu_result  = swap_result;
    6'b00001?:   alu_result  = {27'd0, bitscan_result};
    6'b000001:   alu_result = {31'd0, setcc_result};
    default:     alu_result  = 32'd0;
  endcase

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for selecting next flag values                      //
//                                                                          //
// Multiplexing of next flag values inside the execute stage is performed   //
// by an AND-OR muxing tree for each individual flag. The inputs to the     //
// tree are the computed flag results and the source to be used by a FLAG   //
// instruction.                                                             //
//                                                                          //
// The computed flags are the flag results of each functional unit (which   //
// may or may not set the flag) gated with the microcode bit which selects  //
// that functional unit.                                                    //
//                                                                          //
// For conditional execution, the flag enables are defeated later on,       //
// thereby preventing the flag updates from being accepted into the         //
// committed architectural state.                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : alu_flag_PROC

  x1_min_max_op = x1_min_op_r | x1_max_op_r;
  
  //==========================================================================
  // Z flag as computed in this stage
  //
  alu_z_out     = ( adder_zero                      &  x1_add_op_r          )
                | ( logic_zero                      &  x1_logic_op          )
                | ( barrel_zero                     &  x1_barrel_shift_op_r )
                | ( (swap_result == 32'd0)          &  x1_swap_op_r         )
                | ( bitscan_zero                    &  x1_norm_op_r         )
                ;

  //==========================================================================
  // N flag as computed in this stage
  //
  alu_n_out     = ( adder_negative  & x1_add_op_r   & (!x1_abs_op_r)        )
                | ( (alu_src2 == 32'h80000000)     &  x1_abs_op_r          )
                | ( logic_negative                  &  x1_logic_op          )
                | ( barrel_negative                 &  x1_barrel_shift_op_r )
                | ( swap_result[31]                 &  x1_swap_op_r         )
                | ( bitscan_negative                &  x1_norm_op_r         )
                ;

  //==========================================================================
  // C flag as computed in this stage
  //
  alu_c_out     = (   (adder_carry_out ^ (x1_inv_src2_r | x1_inv_src1_r))
                    & (x1_add_op_r & (!x1_min_max_op) & (!x1_abs_op_r))     )
                | ( (~adder_lessthan)               &  x1_min_op_r          )
                | ( (adder_lessthan | adder_zero)   &  x1_max_op_r          )
                | ( logic_carry                     &  x1_logic_op          )
                | ( alu_src2[31]                   &  x1_abs_op_r          )
                | ( barrel_cout                     &  x1_barrel_shift_op_r )
                ;

  //==========================================================================
  // V flag as computed in this stage
  //
  alu_v_out     = (   adder_overflow  
                    & (x1_add_op_r & (!x1_abs_op_r))                        )
                | ( (alu_src2 == 32'h80000000)     &  x1_abs_op_r          )
                | ( logic_overflow                  &  x1_logic_op          )
                | ( barrel_overflow                 &  x1_barrel_shift_op_r )
                ;
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for computing BRcc outcomes and SETcc results       //
//                                                                          //
// The logic in this process performs the three (or four) fundamental       //
// integer relational comparisons from which the six BRcc conditions are    //
// derived, and from which the eight SETcc conditions are also derived.     //
// This is implemented without using the adder flag results, so that the    //
// path to the brcc_result is minimized. In this logic, the 1,2 or 3 bit    //
// shift of the second source operand is not present in the logic path.     //
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default

always @*
begin : cc_result_PROC
            
  //==========================================================================
  // Compute the three comparisons of (a) equality, (b) signed-less-than,
  // and (c) unsigned-lower.
  //
  eq_test       = (           alu_src1  ==            alu_src2  );  // (a)
  lt_test       = (   $signed(alu_src1) <     $signed(alu_src2) );  // (b)
  lo_test       = ( $unsigned(alu_src1) <   $unsigned(alu_src2) );  // (c)
  
  //==========================================================================
  // The following case statement sets brcc_cond to 1 whenever the 
  // selected BRcc condition is 1, or its inverse is 0. It also
  // prevents brcc_cond from being set when performing BBIT0 or BBIT1
  // (the term ~x1_bit_op_r ensures this for the case element 2'd0).
  //
  case (x1_cc_field_r[2:1])
  2'd0:     brcc_cond = eq_test & (~x1_bit_op_r); // BREQ or BRNE
  2'd1:     brcc_cond = lt_test;                  // BRLT or BRGE
  2'd2:     brcc_cond = lo_test;                  // BRLO or BRHS
  2'd3:     brcc_cond = lt_test | eq_test;        // SETLE or SETGT
  default:  brcc_cond = 1'b0;
  endcase

  //==========================================================================
  // Select one bit from alu_src1, according to the index given by the lower
  // five bits of alu_src2. This signal is then gated with x1_bit_op_r, to
  // form the bbit_result for use in determining the outcome of BBIT0 and BBIT1.
  //
  case (alu_src2[4:0])
  5'd0 : bbit_select = alu_src1[0];
  5'd1 : bbit_select = alu_src1[1];
  5'd2 : bbit_select = alu_src1[2];
  5'd3 : bbit_select = alu_src1[3];
  5'd4 : bbit_select = alu_src1[4];
  5'd5 : bbit_select = alu_src1[5];
  5'd6 : bbit_select = alu_src1[6];
  5'd7 : bbit_select = alu_src1[7];
  5'd8 : bbit_select = alu_src1[8];
  5'd9 : bbit_select = alu_src1[9];
  5'd10 : bbit_select = alu_src1[10];
  5'd11 : bbit_select = alu_src1[11];
  5'd12 : bbit_select = alu_src1[12];
  5'd13 : bbit_select = alu_src1[13];
  5'd14 : bbit_select = alu_src1[14];
  5'd15 : bbit_select = alu_src1[15];
  5'd16 : bbit_select = alu_src1[16];
  5'd17 : bbit_select = alu_src1[17];
  5'd18 : bbit_select = alu_src1[18];
  5'd19 : bbit_select = alu_src1[19];
  5'd20 : bbit_select = alu_src1[20];
  5'd21 : bbit_select = alu_src1[21];
  5'd22 : bbit_select = alu_src1[22];
  5'd23 : bbit_select = alu_src1[23];
  5'd24 : bbit_select = alu_src1[24];
  5'd25 : bbit_select = alu_src1[25];
  5'd26 : bbit_select = alu_src1[26];
  5'd27 : bbit_select = alu_src1[27];
  5'd28 : bbit_select = alu_src1[28];
  5'd29 : bbit_select = alu_src1[29];
  5'd30 : bbit_select = alu_src1[30];
  5'd31 : bbit_select = alu_src1[31];
  endcase
  
  bbit_result = (bbit_select == x1_cc_field_r[0]) & x1_bit_op_r;
  
  //==========================================================================
  // Combine the bbit_result and brcc_cond values, in the final step of 
  // and AND-OR mux structure, and then invert the result if the lsb of
  // the x1_cc_field_r is set to 1. This indicates that the inverse test
  // is required. When performing a BBITn instruction, brcc_cond wil
  // always be 0. This is becahse x1_cc_field_r[2:1] will be 00 and the
  // x1_bit_op_r bit will be set. This will select case 2'd0 above, 
  // in which case brcc_cond will be assigned 0.
  //
  alu_brcc_cond =  bbit_result
                | (brcc_cond ^ (x1_cc_field_r[0] & (~x1_bit_op_r)));
  
  //==========================================================================
  // The result of a SETcc operation is given by the brcc_cond signal,
  // optionally inverted if an odd-numbered `cc' sub-operation is selected.
  //
  setcc_result  = brcc_cond ^ x1_cc_field_r[0];

end
// spyglass enable_block WRN_1024

endmodule // alb_alu
