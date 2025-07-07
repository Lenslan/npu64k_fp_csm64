// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
/////////////////////////////////////////////////////////////
//     16x16 Booth Multiplier with sum and carry out      //
/////////////////////////////////////////////////////////////


//--+----1----+----2----+----3----+----4----+----5----+----6----+----7----+----8
// Booth bit-pair recoding
// Inputs extended to 17-bit to handle unsigned multiply
// Adds one PP for the case of unsigned with MSB=1, total of 9 PP

// Partial products (PP) are extended to 18 bits to accomodate +-2x Booth codes
// Sign extension elimination employed: prefix 111..11 for all PPs, +1 nullifies
//   it for positives (achieved logically-correct arithmetic by inverting the
//   sign bit of the each PP)
// PP0 has a partial sign extension constant, to avoid adding a 10th partial
//   product at its MSB position PP0 sign is not inverted and the next two bits
//   are set to '00' for the constant calculation.
// The constant is as follows:  01010101AB, where A and B are the two bit
//   position immediately after the sign bit of PP0 and they are set as follows:
//   If sign of PP0 is '1' then AB = '01', else AB = '10'
//   This recoding on-the-fly to correct PP0 sign is not a critical path as it
//   executes in parallel with the multi-bit invert and/or shift of the booth
//   select logic.

// leda B_3208 off
// leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator
// LJ:  arithmetic block, verified completely (all input permutations!)
module npuarc_mult16x16_cs35 (
          res_sum, res_carry,
          dataa, datab, signed_op_a, signed_op_b
          );

parameter AIN = 16;
parameter BIN = 16;


// Signed outputs are extended because we sign-extend the partial multiply
// results and must include more bits to cover the larger magnitude of an
// unsigned number with a leading sign bit 0
// In "regular" multiply we drop the digits at 2N and above, because they would
// overflow outside the unsigned result field after adding the sum and carry.
// This is not the case with a multiplier array, where the partial multiply
// results must be extended to the full size of the larger multiply operation.
// Note the "carry" output is shifted in this implementation. It has the same
// number of significant digits as the "sum" output, both represented as
// 2's-complement signed values.

output  [34:0]        res_sum,
                      res_carry;
input   [(AIN-1):0]   dataa;
input   [(BIN-1):0]   datab;
input                 signed_op_a;  // 1 = signed multiply
input                 signed_op_b;

wire    [(AIN-1):0]   a = dataa;

// zero or sign-extend multiplicand
wire    [(BIN):0]     b = {signed_op_b & datab[(BIN-1)], datab[(BIN-1):0]} ;

// wire    [1.5 * (AIN+2) - 1:0] booth_op;
reg     [26:0]        booth_op;     // expand bit pair to 3 bits (1 overlaps)
   
// expand to 3 bit overlapping fields

always @ (a or signed_op_a)
begin:   booth_op_PROC
  booth_op[2:0]   = {a[ 1: 0],1'b0};
  booth_op[5:3]   =  a[ 3: 1];
  booth_op[8:6]   =  a[ 5: 3];
  booth_op[11:9]  =  a[ 7: 5];
  booth_op[14:12] =  a[ 9: 7];
  booth_op[17:15] =  a[11: 9];
  booth_op[20:18] =  a[13:11];
  booth_op[23:21] =  a[15:13];
                                  // sign extend multiplier on-the-fly
  booth_op[26:24] =  signed_op_a ? 3'b0 :  {2'b0,a[15]};
                                  // for signed: 3'b0 has same effect as 3'b111 
end


// to zero out sign for positive PP, concatenated to the SEXT PP;
// booth_op[26:24] never selects a negative partial multiplier: 0 or +x only
wire    [(AIN-1):0] add_one;
assign add_one             = { booth_sign(booth_op[23:21]),
                                booth_sign(booth_op[20:18]),
                                booth_sign(booth_op[17:15]),
                                booth_sign(booth_op[14:12]),
                                booth_sign(booth_op[11:9]),
                                booth_sign(booth_op[8:6]),
                                booth_sign(booth_op[5:3]),
                                booth_sign(booth_op[2:0])
                              };




// function is used to add a 1 at LSB of all negative partial (Booth bit-pair)
// multipliers to complete operation (-A = ~A + 1)
// spyglass disable_block AutomaticFuncTask-ML
// SMD: Function variables are static and could be overriden
// SJ:  These functions are local to modules so no risk of being overriden
function [1:0] booth_sign;
// spyglass enable_block AutomaticFuncTask-ML
input    [2:0] booth_op;
begin
        case (booth_op)
                3'b100 :         booth_sign = 2'b01 ;   // -2
                3'b101, 3'b110 : booth_sign = 2'b01 ;   // -1
                default :        booth_sign = 2'b00 ;   //  0 or positive
        endcase
end
endfunction
 

//
// spyglass disable_block AutomaticFuncTask-ML
// SMD: Function variables are static and could be overriden
// SJ:  These functions are local to modules so no risk of being overriden
function [(BIN+2):0]    booth_operand;  // one bit added for 2x and one bit for
                                        // added '1' at MSB+1 for sign extension
                                        // constant
// spyglass enable_block AutomaticFuncTask-ML
input    [(BIN):0]      bop;
input    [2:0]          booth_op;

// multiplicand is 17 bits (adds 0 for unsigned), booth_operand is 19 bits
// sign extension elimination, add two bits: invert sign bit at position MSB and
// append '1' to MSB+1 position.
// PP0 does not invert sign, see later details for a 'trick fix'

begin
  case (booth_op)
    3'b000:  booth_operand = {2'b11,  17'b0                            }; // +0
    3'b001:  booth_operand = {1'b1 , ~bop[(BIN)],  bop[(BIN):0]        }; // +x
    3'b010:  booth_operand = {1'b1 , ~bop[(BIN)],  bop[(BIN):0]        }; // +x
    3'b011:  booth_operand = {1'b1 , ~bop[(BIN)],  bop[(BIN-1):0], 1'b0}; // +2x

    3'b100:  booth_operand = {1'b1 ,  bop[(BIN)], ~bop[(BIN-1):0], 1'b1}; // -2x
    3'b101:  booth_operand = {1'b1 ,  bop[(BIN)], ~bop[(BIN):0]        }; // -x
    3'b110:  booth_operand = {1'b1 ,  bop[(BIN)], ~bop[(BIN):0]        }; // -x
    3'b111:  booth_operand = {2'b11,  17'b0};                             // +0

    default: booth_operand = {2'b11,  17'b0};                             // +0
  endcase
end
endfunction


/////////////////////////////////////////////////////////////////////////////
// Generation of partial products with "sign extension elimination" prefix:
// Add 2 bits: invert sign bit at position MSB and append '1' to MSB+1 position

// PP0 must be corrected: standard algorithm requires adding '1' at to PP0
//   position MSB (sign extension constant 10101011); this would require adding
//   a 10th PP at that bit position and increase critical path.
// Trick fix: PP0 sign is not inverted and only a partial sign extension is
//   appended to it, in the following format:
//        11111..1110[PP0_sgn][PP0...]
// If PP0_sgn is 1 then we need to convert the 0 to 1.
// If PP0_sgn is 0 then we need to add +1 at the next position (i.e. the first
//   1) to nullify the string of 1's.
// This may seem complex but it ends up being quite simple. Re-calculating the
//   sign extension constant for all 9 PPs gives us a simple 10101010..101000
//   (last zero aligns with PP0_sgn). This constant treats all PPs other than
//   PP0 just like the "standard" algorithm, i.e. invert the sign bit and append
//   1 at the next bit position.
// Since only 00 is appended to the PP0 extension, correcting it as outlined
//   above is simple and basically converts these two bits to 10 (PP0_sgn==0) or
//   01 (PP0_sgn==1). PP0_sgn is pre-calculated, although synthesis may speed it
//   up anyway.
// This is a simple modification which retains the structure of 9 PPs and
//   therefore the first level of the Wallace tree is made of CSA3_to_2 only.
// Timing budget is not increased (same as the "textbook" algorithm).


// op1_1 is PP0, _pre is before correction for PP0
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  arithmetic signals
wire [(BIN+2):0]  op1_1_pre;
// leda NTL_CON13A on
assign   op1_1_pre  = booth_operand(b,booth_op[2:0]);

// speed up calculation of the sign rather than wait for the (slow) mux logic
wire              op1_1_sgn;
assign       op1_1_sgn      = ((booth_op[2:0] == 3'b0) ||
                                (booth_op[2:0] == 3'b111)  ) ?
                               1'b0 :
                               add_one[0] ^ b[16];
                                     // add_one[0]:  1 = negative code (-x, -2x)
                                     // b[16] is the sign bit of multiplicand

// sign bit extends to 3 bits to perform the modified sign extension algorithm
// (bits AB replace the "standard" constant)
//wire [(BIN+4):0] op1_1={1'b0,~op1_1_sgn,op1_1_sgn,op1_1_sgn,op1_1_pre[16:0]};
wire [(BIN+3):0]  op1_1;
assign    op1_1   = {~op1_1_sgn,op1_1_sgn,op1_1_sgn,op1_1_pre[16:0]};

// All other PPs conform to the standard algorithm including +1 for negating
// previous PP and sign extension elimintion constant.
// Note that PPs extend beyond the range of the result components, so we can
// compute overflow

wire [(BIN+4):0]  op1_2;
assign            op1_2  = { booth_operand(b,booth_op[5:3]),
                                                         add_one[1:0]         };

// length of booth_operand plus 2 LSB for "add_one" from op_1_2 plus proper
// shift to place it at the correct (radix-4) bit position
wire [(BIN+6):0]  op1_3;
assign            op1_3  = { booth_operand(b,booth_op[8:6]),
                                                         add_one[3:2],    2'b0};

wire [(BIN+8):0]  op1_4;
assign            op1_4  = { booth_operand(b,booth_op[11:9]),
                                                         add_one[5:4],    4'b0};

wire [(BIN+10):0] op1_5;
assign            op1_5  = { booth_operand(b,booth_op[14:12]),
                                                         add_one[7:6],    6'b0};

wire [(BIN+12):0] op1_6;
assign            op1_6  = { booth_operand(b,booth_op[17:15]),
                                                         add_one[9:8],    8'b0};

wire [(BIN+14):0] op1_7;
assign            op1_7  = { booth_operand(b,booth_op[20:18]),
                                                         add_one[11:10], 10'b0};

wire [(BIN+16):0] op1_8;
assign            op1_8  = { booth_operand(b,booth_op[23:21]),
                                                         add_one[13:12], 12'b0};

// This is the unsigned PP
wire [(BIN+18):0] op1_9;
assign            op1_9  = { booth_operand(b,booth_op[26:24]),
                                                         add_one[15:14], 14'b0};

// spyglass disable_block W116
// SMD: Length of the operands are unequal
// SJ:  extended field calculation with zero extension, cannot overflow/underflow

/////////////////////////////////////////////////////////////////////////////
// Wallace tree reduces 9 PPs to 2 components in the following manner:
// 9PP -> 3:2 -> 6PP -> 3:2 -> 4PP -> 4:2 -> 2PP (sum, carry)
// Equations are written as generic RTL
// Synthesis reduces trailing and leading zeroes efficiently, so there is no
// need to specify accurate bit-fields or manually reduce logic at certain
// bit positions

/* Wallace Tree, stage 1:  9 PP, 3x CSA32 */

wire [(BIN+6):0] op2_1;
assign op2_1 = op1_1 ^ op1_2 ^ op1_3; 
wire [(BIN+7):0] op2_2;
assign op2_2 = {(op1_1 & op1_2) | (op1_1 & op1_3) | (op1_2 & op1_3),
                                                                          1'b0}; 

wire [(BIN+12):0] op2_3;
assign op2_3 = op1_4 ^ op1_5 ^ op1_6; 
wire [(BIN+13):0] op2_4;
assign op2_4 = {(op1_4 & op1_5) | (op1_4 & op1_6) | (op1_5 & op1_6), 
                                                                          1'b0}; 

wire [(BIN+18):0] op2_5;
assign op2_5 = op1_7 ^ op1_8 ^ op1_9; 
wire [(BIN+19):0] op2_6;
assign op2_6 = {(op1_7 & op1_8) | (op1_7 & op1_9) | (op1_8 & op1_9),
                                                                          1'b0}; 


/* Wallace Tree, stage 2:  6 IP, 2x CSA32 */

wire [(BIN+12):0] op3_1;
assign op3_1 = op2_1 ^ op2_2 ^ op2_3; 
wire [(BIN+13):0] op3_2;
assign op3_2 = {(op2_1 & op2_2) | (op2_1 & op2_3) | (op2_2 & op2_3), 
                                                                          1'b0}; 

wire [(BIN+19):0] op3_3;
assign op3_3 = op2_4 ^ op2_5 ^ op2_6; 


// leda BTTF_D002 off
// LMD: unequal length LHS and RHS in assignment
// LJ:  waiver LHS > RHS, due to zero extension of intermediate partial products
// spyglass disable_block W164b
// SMD: unequal length LHS and RHS in assignment
// spyglass disable_block W164a
// SMD: unequal length LHS and RHS in assignment
// SJ:  
wire [(BIN+19):0] op3_4;
assign op3_4 = {(op2_4 & op2_5) | (op2_4 & op2_6) | (op2_5 & op2_6), 
                                                                          1'b0}; 

/* Wallace Tree, stage 3:  4 IP, 1x CSA42 */

// intermediate carry
wire [(BIN+19):0] tc0;
assign tc0   =  {op3_1 & op3_2  | op3_1 & op3_3  | op3_2 & op3_3,
                                                                          1'b0}; 
//sum
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  arithmetic signals
wire [(BIN+19):0] op4_1;
assign op4_1 =  op3_1 ^ op3_2 ^ op3_3 ^ op3_4 ^ tc0;

//carry
wire [(BIN+19):0] op4_2;
assign op4_2 =  {(op3_1 ^ op3_2 ^ op3_3 ^ op3_4) & tc0 |
                           (~(op3_1 ^ op3_2 ^ op3_3 ^ op3_4)) & op3_4,
                                                                          1'b0}; 
// leda NTL_CON13A on
// leda BTTF_D002 on
// spyglass enable_block W116
// spyglass enable_block W164b
// spyglass enable_block W164a
/* Output */

// Correct both negative sign bits for sum and carry result of unsigned
// multiply - arithmetic overflow anomaly
// This logic is outside the critical path (middle bits) of the array
wire sgn_sum;
assign sgn_sum   = !signed_op_a && (!signed_op_b) ?
                                                op4_1[34] & (~op4_2[34]) :
                                                op4_1[34]; 
wire sgn_carry;
assign sgn_carry = !signed_op_a && (!signed_op_b) ?
                                                op4_2[34] & (~op4_1[34]) :
                                                op4_2[34]; 

assign   res_sum   =  {sgn_sum,   op4_1[33:0]} ;
assign   res_carry =  {sgn_carry, op4_2[33:0]} ;


endmodule
// leda B_3200 on
// leda B_3208 on
