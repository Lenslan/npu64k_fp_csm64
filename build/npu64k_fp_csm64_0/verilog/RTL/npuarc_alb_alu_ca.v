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

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_alu_ca (
  ////////// source data inputs at Commit stage //////////////////////////////
  //  
  input      [`npuarc_DATA_RANGE]        src0_lo,          // operand 1 [31:0]
  input      [`npuarc_DATA_RANGE]        src1_lo,          // operand 2 [31:0]
  input      [`npuarc_DATA_RANGE]        ca_res_r,         // early result (linkage)
  input      [`npuarc_DATA_RANGE]        src0_hi,          // operand 1 [63:32]
  input      [`npuarc_DATA_RANGE]        src1_hi,          // operand 2 [62:32]
  input                           src0_hi_65,       // 65th bit for overflow
  input                           src1_hi_65,       // 65th bit for overflow
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]        ar_aux_status32_r,//
// leda NTL_CON13C on
  ////////// ALU control inputs from Commit stage ////////////////////////////
  //  
  input      [`npuarc_CA_P0_RANGE]       ca_p0_r,          // src1 half-word invert
  input      [`npuarc_CA_P1_RANGE]       ca_p1_r,          // src2 half-word invert
  input      [`npuarc_CA_P2_RANGE]       ca_p2_r,          // src1 half-word join
  input      [`npuarc_CA_P3_RANGE]       ca_p3_r,          // src2 half-word join
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]        byp_acc_hi,       // up-to-date ACCH
// leda NTL_CON13C on
  input                           v_flag,           // CA-stage V flag
  input                           ca_cin_r,         // addr carry-in.

  ////////// ucode inputs from Commit stage //////////////////////////////////
  //  
  input                           ca_add_op_r,  
  input                           ca_bit_op_r,  
  input                           ca_mask_op_r,
  input                           ca_inv_src1_r, 
  input                           ca_inv_src2_r, 
  input                           ca_or_op_r,
  input                           ca_and_op_r,
  input                           ca_xor_op_r,
  input                           ca_mov_op_r,
  input                           ca_signed_op_r,
  input                           ca_vec_shimm_r,
  input                           ca_src2_mask_sel_r, 
  input                           ca_byte_size_r,
  input                           ca_half_size_r,
  input                           ca_simple_shift_op_r,
  input                           ca_left_shift_r,
  input                           ca_rotate_op_r,
  input                           ca_with_carry_r,
  input                           ca_link_r,
  input  [2:0]                    ca_cc_field_r,
  input                           ca_setcc_op_r,
  input                           ca_mpy_op_r,
  input                           ca_acc_wenb_r,
  input                           ca_acc_op_r,
  input                           ca_vector_op_r,
  input                           ca_dual_op_r,
  input                           ca_prod_sign_r,
  input                           ca_quad_op_r,
  input                           ca_scond,
  input                           dmp_scond_zflag,
                 
  ////////// result and status outputs ///////////////////////////////////////
  //  
  output reg [`npuarc_DATA_RANGE]        result_lo,        // result to Rn
  output reg [`npuarc_DATA_RANGE]        result_hi,        // paired result to Rn+1
  output     [`npuarc_DATA_RANGE]        alu_acch_res,     // result for ACCH
  output reg [`npuarc_ZNCV_RANGE]        result_zncv,      // result flags
  output reg                      alu_brcc_cond     // BRcc,BBIT,SETcc result
);

// Unused reg/wires for syntax. Disable linting as appropriate.
//
//reg                           unused_0;
//reg                           unused_1;

// @alu_addr_PROC
//
reg [`npuarc_DOUBLE_RANGE]           src_0;            // SRC0 operand
reg [`npuarc_DOUBLE_RANGE]           src_1;            // SRC1 operand
reg [`npuarc_DATA_RANGE]             src1_sh;
reg [67:0]            adder_src0;      //
reg [67:0]            adder_src1;      //

reg                           adder_cout;       //
// leda NTL_CON13A off
// leda NTL_CON12A off
// leda NTL_CON12 off
// LMD: undriven internal net
// LJ:  Arithmetic module with unused bit
reg [67:0]            adder_result;     //
reg [`npuarc_DATA_RANGE]             adder_result_hi;  //
// leda NTL_CON12A on
// leda NTL_CON12 on
reg                           adder_cout_hi;    //

// leda NTL_CON12A off
// leda NTL_CON12 off
// LMD: undriven internal net
// LJ:  Arithmetic module with not used bit
reg [`npuarc_DATA_RANGE]             adder_result_lo;  //
// leda NTL_CON12A on
// leda NTL_CON12 on
// leda NTL_CON13A on
reg                           adder_z;          //
reg                           adder_n;          //
reg                           adder_c;          //
reg                           arith_v;          //
reg                           adder_v;          //
//reg                           prod_sign;        //
reg                           trans64_v;        //
reg                           arith64_v;        //

// @alb_logic_PROC
//
reg  [`npuarc_DATA_RANGE]            logic_src1;
reg  [`npuarc_DATA_RANGE]            logic_src2;

// alb_maskgen:
//
wire [`npuarc_DATA_RANGE]            ca_bit_mask;      //

// alb_logic_unit:
//
wire [`npuarc_DATA_RANGE]            logic_result;     //
wire                          logic_zero;       //
wire                          logic_negative;   //
wire                          logic_carry;      //
wire                          logic_overflow;   //

// @alu_result_PROC
//
reg                           ca_logic_op;      //
reg                           logic_or_link;    //
reg  [`npuarc_DATA_RANGE]            ll_result;        // logic or linkage result

// @alu_flag_PROC
//
reg                           ca_adder_op;      // ADD, SUB, MPY user adder
reg                           adder_lt;         //
reg                           alu_z_out;        // Zero result from ALU
reg                           alu_n_out;        // Negative result from ALU
reg                           alu_c_out;        // Carry result from ALU
reg                           alu_v_out;        // oVerflow result from ALU

// @ca_cc_PROC
//
// BRcc condition-decode signals, defined one-hot to optimize timing
//
reg                           eq_test;          // BREQ or SETEQ condition
reg                           lt_test;          // BRLT or SETLT condition
reg                           lo_test;          // BRLO or SETLO condition
reg                           brcc_cond;        // pre-inversion BRcc result
reg                           bbit_select;      // pre-gating BBITn result
reg                           bbit_result;      // gated BBITn result
reg                           setcc_result;     // result of a SETcc instr.

// @mask_opd_sel_PROC
//
reg   [4:0]                   mask_src;         // maskgen source input
reg                           ca_xbfu_op;       // XBFU operation is decoded


wire ca_mpyh_r;
assign   ca_mpyh_r   = ca_mpy_op_r & ca_byte_size_r;
reg  sel_adder_hi;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to select maskgen inputs                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : mask_opd_sel_PROC

  mask_src          = src1_lo[4:0];
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Adder                                                                    //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: alu_adder_PROC

  //==========================================================================
  // Select the source operand values for the adder.
  //
  src1_sh           = src1_lo;

  src_0             = {  src0_hi[31:1],
                         (ca_mpy_op_r | ca_vector_op_r) ? src0_hi[0] : 1'b0,
                         src0_lo
                      }
                    ;

  src_1             = {  src1_hi[31:1],
                         (ca_mpy_op_r | ca_vector_op_r) ? src1_hi[0] : 1'b0,
                         src1_sh
                      }
                    ;

  adder_src0        = {  src0_hi_65
                       , (src_0[63:48] ^ {16{ca_p0_r[3]}}), ca_p2_r[2]
                       , (src_0[47:32] ^ {16{ca_p0_r[2]}}), ca_p2_r[1]
                       , (src_0[31:16] ^ {16{ca_p0_r[1]}}), ca_p2_r[0]
                       , (src_0[15:0]  ^ {16{ca_p0_r[0]}})
                      }
                    ;

  adder_src1        = {  src1_hi_65
                       , (src_1[63:48] ^ {16{ca_p1_r[3]}}), ca_p3_r[2]
                       , (src_1[47:32] ^ {16{ca_p1_r[2]}}), ca_p3_r[1]
                       , (src_1[31:16] ^ {16{ca_p1_r[1]}}), ca_p3_r[0]
                       , (src_1[15:0]  ^ {16{ca_p1_r[0]}})
                      }
                    ;

  //==========================================================================
  // Calculate sum and carry-out using an inferred adder.
  //
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y   (Obsolete)
// LJ:  LHS always has 1 bit more than RHS, to capture carry-out
// leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator
// LJ:  LHS always has 1 bit more than RHS, to capture carry-out
// spyglass disable_block W164b
// SMD: Unequal length LHS and RHS in assignment
  {   adder_cout_hi
    , adder_result }    = adder_src0 + adder_src1 + ca_cin_r;
// leda B_3200 on
// leda B_3208 on
// spyglass enable_block W164b

  adder_cout            = adder_result[33];

  //==========================================================================
  // Combined adder sub-words to form the word-sized results
  //
  adder_result_hi = {adder_result[66:51], adder_result[49:34]};
  adder_result_lo = {adder_result[32:17], adder_result[15:0] };

  //==========================================================================
  // Derive Zero-flag for adder 
  //
  adder_z      = ca_mpyh_r
               ? (adder_result_hi == `npuarc_DATA_SIZE'd0)
               : (adder_result_lo == `npuarc_DATA_SIZE'd0)
               ;

  //==========================================================================
  // Derive Negative-flag for adder
  // 
  adder_n      = ((~ca_mpy_op_r) | ca_signed_op_r)
               & (ca_mpy_op_r ? adder_result_hi[31] : adder_result_lo[31])
               ;

  //==========================================================================
  // Derive Carry-flag for adder
  //
  adder_c      = adder_cout
               ^ (ca_inv_src1_r | ca_inv_src2_r)
               ;

  //==========================================================================
  // Derive Overflow-flag based on the result from the adder and the sign
  // of the source operands.
  // 
  // When the CA-stage adder is used to perform the final step of a multiply
  // operation, the overflow flag is derived as follows for each type of mpy:
  //
  //  (a) mpyu: V = res[63:32] == 32'b0          i.e. zero extension only
  //  (b) mpy:  V = res[63:32] == {32{res[31]}}  i.e. sign extension only
  //  (c) mpym: V = 0
  //  (d) mpyw: V = 0
  //  (e) any mpy that initializes the accumulator: V = 0
  //  (f) macu, macdu: V |= 65th bit of the 64-bit final sum
  //  (g) other unsigned mac: V |= (acc msb transitions from 1 to 0)
  //  (h) signed mac:   V |= (signed result not representable in 64 bits)
  // 
  arith_v = (   (adder_result_lo[31] != adder_src1[32])
              & (adder_src0[32] == adder_src1[32]))
          ;
  //==========================================================================
  // trans64_v is asserted in those cases where a signed MAC operation would
  // overflow if there is a change of sign in the accumulator.
  //
  trans64_v = (ca_dual_op_r | ca_quad_op_r)
            ? (byp_acc_hi[31] ^ byp_acc_hi[30])
            : (ca_prod_sign_r == byp_acc_hi[31])
            ;
            
  //==========================================================================
  // arith64_v is asserted if there is an overflow, assuming a signed MAC
  // operation is in progress.
  //
  arith64_v = trans64_v 
            & (byp_acc_hi[31] !=  adder_result_hi[31])
            ;

  casez ({  ca_mpy_op_r,    ca_acc_op_r,    ca_acc_wenb_r,
            ca_signed_op_r, ca_vec_shimm_r, ca_half_size_r, ca_byte_size_r
         })
  7'b100_0?00: adder_v = (adder_result_hi != 32'h0);                       // (a)
  7'b100_1?00: adder_v = (adder_result_hi != {32{adder_result_lo[31]}});   // (b)
  7'b100_??01: adder_v = 1'b0;                                             // (c)
  7'b100_??1?: adder_v = 1'b0;                                             // (d)
  //
  7'b101_????: adder_v = 1'b0;                                             // (e)
  7'b11?_00??: adder_v = v_flag | adder_result[67];                // (f)
  7'b11?_01??: adder_v = v_flag | (!adder_result_hi[31] & byp_acc_hi[31]); // (g)
  7'b11?_1???: adder_v = v_flag | arith64_v;                               // (h)
  default:     adder_v = arith_v; 
  endcase

  //==========================================================================
  // Derive 'less than' condition for use in min/max/abs operations.
  //
  adder_lt    = adder_result_lo[31] != arith_v;
  
end // block: alu_adder_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Logic Unit                                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: alb_logic_PROC

  //==========================================================================
  // Derive inputs to logic-unit, optionally inverted as required.
  //
  logic_src1   = src0_lo ^ {`npuarc_DATA_SIZE{ca_inv_src1_r}};
  logic_src2   = src1_lo ^ {`npuarc_DATA_SIZE{ca_inv_src2_r}};

end // block: alb_logic_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Maskgen Unit                                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_maskgen u_alb_maskgen (
  .src2_val           (mask_src             ),
  .bit_op             (ca_bit_op_r          ),
  .mask_op            (ca_mask_op_r         ),
  .inv_mask           (ca_inv_src2_r        ),
  .mask_result        (ca_bit_mask          )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Logic Unit                                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


npuarc_alb_logic_unit u_alb_logic_unit (
  .src1               (logic_src1                ),
  .src2               (logic_src2                ),
  .src2_mask          (ca_bit_mask               ),
  .carry_flag         (ar_aux_status32_r[`npuarc_C_FLAG]),
  .or_op              (ca_or_op_r                ),
  .and_op             (ca_and_op_r               ),
  .xor_op             (ca_xor_op_r               ),
  .mov_op             (ca_mov_op_r               ),
  .signed_op          (ca_signed_op_r            ),
  .mask_sel           (ca_src2_mask_sel_r        ),
  .byte_size          (ca_byte_size_r            ),
  .half_size          (ca_half_size_r            ),
  .shift_op           (ca_simple_shift_op_r      ),
  .left               (ca_left_shift_r           ),
  .rotate             (ca_rotate_op_r            ),
  .with_carry         (ca_with_carry_r           ),
  .result             (logic_result              ),
  .zero               (logic_zero                ),
  .negative           (logic_negative            ),
  .carry              (logic_carry               ),
  .overflow           (logic_overflow            )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// ALU result consolidator                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


always @*
begin: alu_result_PROC

  //==========================================================================
  //
  ca_logic_op     = ca_mov_op_r
                  | ca_or_op_r
                  | ca_and_op_r
                  | ca_xor_op_r
                  | ca_simple_shift_op_r
                  ;

  logic_or_link   = ca_logic_op | ca_link_r;
  
  ll_result       = ca_link_r ? ca_res_r : logic_result;
  
  //==========================================================================
  // Select the 32 bits of the CA-stage ALU result that will be assigned to
  // the higher-numbered (odd) destination register within a register pair.
  //
  result_hi       = adder_result_hi;  // *** BYTE_ORDER == HS_LITTLE_ENDIAN ***

  //==========================================================================
  // Select the 32 bits of the CA-stage ALU result that will be assigned to
  // the CA-stage result bus (result_lo).
  // When selecting the result of MPYH or MPYHU, the ca_mpyh_r signal is
  // asserted, and this causes result_lo to be assigned adder_result_hi.
  //
  // When returning a 64-bit register-pair, this case statement selects the
  // value to assign the lower-numbered (even) destination register within
  // the register pair. This depends on the configured byte ordering; a big
  // endian system selects adder_result_hi, whereas a little-endian system
  // selects adder_result_lo.
  //
  sel_adder_hi    = ca_mpyh_r
                  ; 
 
  
  casez ({  
            2'b00
           ,logic_or_link 
           ,ca_setcc_op_r
           ,sel_adder_hi
          ,3'b000        
         }) 
    8'b001?????: result_lo = ll_result;
    8'b0001????: result_lo = {31'd0, setcc_result};
    8'b00001???: result_lo = adder_result_hi;
    default:     result_lo = adder_result_lo;
  endcase

end // block: alu_result_PROC

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

  ca_adder_op       = ca_add_op_r
                    | ca_mpy_op_r
                    ;

  //==========================================================================
  // Z flag as computed in this stage
  //
  alu_z_out     = ( adder_z                & ca_adder_op          & !ca_scond)
                | ( logic_zero             & ca_logic_op          & !ca_scond)
                | ( ca_scond               & dmp_scond_zflag                 )
                ;

  //==========================================================================
  // N flag as computed in this stage
  //
  alu_n_out     = ( adder_n                         &  ca_adder_op          )
                | ( logic_negative                  &  ca_logic_op          )
                ;

  //==========================================================================
  // C flag as computed in this stage
  //
  alu_c_out     = ( adder_c                         &  ca_adder_op          )
                | ( logic_carry                     &  ca_logic_op          )
                ;

  //==========================================================================
  // V flag as computed in this stage
  //
  alu_v_out     = ( adder_v                         &  ca_adder_op          )
                | ( logic_overflow                  &  ca_logic_op          )
                ;
  
  //==========================================================================
  // Combine flag results into flag output vector
  //
  result_zncv   = { alu_z_out, alu_n_out, alu_c_out, alu_v_out };

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

always @*
begin : ca_cc_PROC
            
// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function
// SJ:  argument unsigned by default, causes no problems
  //==========================================================================
  // Compute the three comparisons of (a) equality, (b) signed-less-than,
  // and (c) unsigned-lower.
  //
  eq_test       = (           src0_lo  ==            src1_lo  );    // (a)
  lt_test       = (   $signed(src0_lo) <     $signed(src1_lo) );    // (b)
  lo_test       = ( $unsigned(src0_lo) <   $unsigned(src1_lo) );    // (c)
  
  //==========================================================================
  // The following case statement sets brcc_cond to 1 whenever the 
  // selected BRcc condition is 1, or its inverse is 0. It also
  // prevents brcc_cond from being set when performing BBIT0 or BBIT1
  // (the term ~x1_bit_op_r ensures this for the case element 2'd0).
  //
// spyglass enable_block WRN_1024
  case (ca_cc_field_r[2:1])
  2'd0:     brcc_cond = eq_test & (~ca_bit_op_r); // BREQ or BRNE
  2'd1:     brcc_cond = lt_test;                  // BRLT or BRGE
  2'd2:     brcc_cond = lo_test;                  // BRLO or BRHS
  2'd3:     brcc_cond = lt_test | eq_test;        // SETLE or SETGT
  default:  brcc_cond = 1'b0;
  endcase

  //==========================================================================
  // Select one bit from src0_lo, according to the index given by the lower
  // five bits of src1_lo. This signal is then gated with x1_bit_op_r, to
  // form the bbit_result for use in determining the outcome of BBIT0 and BBIT1.
  //
  case (src1_lo[4:0])
  5'd0 : bbit_select = src0_lo[0];
  5'd1 : bbit_select = src0_lo[1];
  5'd2 : bbit_select = src0_lo[2];
  5'd3 : bbit_select = src0_lo[3];
  5'd4 : bbit_select = src0_lo[4];
  5'd5 : bbit_select = src0_lo[5];
  5'd6 : bbit_select = src0_lo[6];
  5'd7 : bbit_select = src0_lo[7];
  5'd8 : bbit_select = src0_lo[8];
  5'd9 : bbit_select = src0_lo[9];
  5'd10 : bbit_select = src0_lo[10];
  5'd11 : bbit_select = src0_lo[11];
  5'd12 : bbit_select = src0_lo[12];
  5'd13 : bbit_select = src0_lo[13];
  5'd14 : bbit_select = src0_lo[14];
  5'd15 : bbit_select = src0_lo[15];
  5'd16 : bbit_select = src0_lo[16];
  5'd17 : bbit_select = src0_lo[17];
  5'd18 : bbit_select = src0_lo[18];
  5'd19 : bbit_select = src0_lo[19];
  5'd20 : bbit_select = src0_lo[20];
  5'd21 : bbit_select = src0_lo[21];
  5'd22 : bbit_select = src0_lo[22];
  5'd23 : bbit_select = src0_lo[23];
  5'd24 : bbit_select = src0_lo[24];
  5'd25 : bbit_select = src0_lo[25];
  5'd26 : bbit_select = src0_lo[26];
  5'd27 : bbit_select = src0_lo[27];
  5'd28 : bbit_select = src0_lo[28];
  5'd29 : bbit_select = src0_lo[29];
  5'd30 : bbit_select = src0_lo[30];
  5'd31 : bbit_select = src0_lo[31];
  endcase
  
  bbit_result = (bbit_select == ca_cc_field_r[0]) & ca_bit_op_r;
  
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
                | (brcc_cond ^ (ca_cc_field_r[0] & (~ca_bit_op_r)));
  
  //==========================================================================
  // The result of a SETcc operation is given by the brcc_cond signal,
  // optionally inverted if an odd-numbered `cc' sub-operation is selected.
  //
  setcc_result  = brcc_cond ^ ca_cc_field_r[0];

end

assign  alu_acch_res  = adder_result_hi; // result for ACCH

endmodule // alb_alu_ca
