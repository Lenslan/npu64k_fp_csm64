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
//    ##     ####   #    #
//   #  #   #    #  #    #
//  #    #  #       #    #
//  ######  #  ###  #    #
//  #    #  #    #  #    #
//  #    #   ####    ####
//
// ===========================================================================
//
// Description:
//
//  The AGU module implements the address adder for the ARCv2 instruction set.
//  It computes the sum of a base address (or long immediate value) and an
//  optionally-scaled offset, which may be a full 32-bit register value in
//  some cases. It also computes the address of the next word accessed beyond
//  the computed address, so support non-aligned accesses. This will be the
//  address+4 when LL64_OPTION == 0, or address+8 when LL64_OPTION == 1.
//
//  This module constains no state elements.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_agu (

  ////////// Input values for the AGU operation //////////////////////////////
  //
  input   [`npuarc_ADDR_RANGE]     agu_src1,           // AGU source operand 1
  input   [`npuarc_ADDR_RANGE]     agu_src2,           // AGU source operand 2

  ////////// Microcode control signals for the AGU ///////////////////////////
  //
  input                     x1_src2_sh1_r,      // scale src2 by 2
  input                     x1_src2_sh2_r,      // scale src2 by 4
  input                     x1_pre_addr_r,      // pre-update addressing mode
  input                     x1_mov_op_r,        // overloaded ucode bit (EX)
  
  ////////// Control signals for the AGU bank sel ///////////////////////////
  //
  input                     x1_byte_size_r,  
  input                     x1_half_size_r,  
  input                     x1_double_size_r,
  ////////// Result outputs from the AGU operation ///////////////////////////
  //
  output reg [`npuarc_ADDR_RANGE]  agu_addr0,          // calculated address
  output reg [`npuarc_ADDR_RANGE]  agu_addr1,          // agu_addr0 plus 4 or 8
  output reg [1:0]          agu_bank_sel_lo,    // bank sel
  output reg [1:0]          agu_bank_sel_hi     // bank sel
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Wires and regs for local non-registered signals                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_ADDR_RANGE]           agu_src2_addr0_sh0;
reg [`npuarc_ADDR_RANGE]           agu_src2_addr0_sh1;
reg [`npuarc_ADDR_RANGE]           agu_src2_addr0_sh2;

reg [`npuarc_ADDR_RANGE]           agu_src2_addr1_sh0;
reg [`npuarc_ADDR_RANGE]           agu_src2_addr1_sh1;
reg [`npuarc_ADDR_RANGE]           agu_src2_addr1_sh2;

reg [`npuarc_ADDR_RANGE]           agu_addr0_sh0;
reg [`npuarc_ADDR_RANGE]           agu_addr0_sh1;
reg [`npuarc_ADDR_RANGE]           agu_addr0_sh2;

reg [`npuarc_ADDR_RANGE]           agu_addr1_sh0;
reg [`npuarc_ADDR_RANGE]           agu_addr1_sh1;
reg [`npuarc_ADDR_RANGE]           agu_addr1_sh2;

reg [3:0]                   agu_src1_sh0;
reg [3:0]                   agu_src2_sh0;

wire [3:0]                  x1_bank_sel_sh0;
wire [3:0]                  x1_bank_sel_sh1;
wire [3:0]                  x1_bank_sel_sh2;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process optionally-shift the address offset, which is the   //
// second source operand, as required by either the addressing mode.        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
//  Pre-computation of the src2 shifting 
//   
//////////////////////////////////////////////////////////////////////////////
always @*
begin : addr0_opd_sh_PROC
  agu_src2_addr0_sh0 = agu_src2;
  agu_src2_addr0_sh1 = {agu_src2[30:0],   1'b0};
  agu_src2_addr0_sh2 = {agu_src2[29:0],  2'b00};
  
end

always @*
begin : addr1_opd_sh_PROC
  // When using the .AB mode (post-update), the x1_src2_sh1_r and x1_src2_sh2_r
  // signals are guaranteed to be 0. In this specific case we also require that
  // addr1_src2 is zero. This is to allow the agu_addr1 output to be simply
  // agu_src1 + C, where C is either 4 or 8 (depending on whether LL64_OPTION
  // is enabled). Therefore, when the .AB mode is selected, the no_src2_shift
  // control signal is also set to 0. This ensures that none of the gating
  // signals for agu_src2 is enabled, and thus addr1_src2 is zero.
  //
  agu_src2_addr1_sh0 = agu_src2 & {32{~x1_pre_addr_r}};
  agu_src2_addr1_sh1 = {agu_src2[30:0],   1'b0};
  agu_src2_addr1_sh2 = {agu_src2[29:0],  2'b00};
end

//////////////////////////////////////////////////////////////////////////////
// Compute the effective address plus 4 or 8. This value is required when
// performing non-aligned memory operations that may require two successive
// words to be read.
// Synthesis will map this to an independent adder, prefixed with
// a single CSA stage. Optimization using a flagged prefix adder
// may also be possible.
//////////////////////////////////////////////////////////////////////////////
always @*
begin : agu_adder_PROC
// spyglass disable_block W484, W164a
// LMD:  Possible loss of carry
// LJ: carry is impossible or a mathematical dont_care

// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y  
// LJ:  address addition is modulo 2^32, so carry-out should be ignored
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  address addition is modulo 2^32, so carry-out should be ignored

  agu_addr0_sh0  = agu_src1[`npuarc_ADDR_RANGE]            
                 + agu_src2_addr0_sh0[`npuarc_ADDR_RANGE]; 
  agu_addr0_sh1  = agu_src1[`npuarc_ADDR_RANGE]            
                 + agu_src2_addr0_sh1[`npuarc_ADDR_RANGE]; 
  agu_addr0_sh2  = agu_src1[`npuarc_ADDR_RANGE]            
                 + agu_src2_addr0_sh2[`npuarc_ADDR_RANGE]; 

  agu_addr1_sh0  = agu_src1[`npuarc_ADDR_RANGE] 
                 + agu_src2_addr1_sh0[`npuarc_ADDR_RANGE] 
                 + 8;
  agu_addr1_sh1  = agu_src1[`npuarc_ADDR_RANGE] 
                 + agu_src2_addr1_sh1[`npuarc_ADDR_RANGE] 
                 + 8;
  agu_addr1_sh2  = agu_src1[`npuarc_ADDR_RANGE] 
                 + agu_src2_addr1_sh2[`npuarc_ADDR_RANGE] 
                 + 8;
// leda W484 on
// leda BTTF_D002 on
// spyglass enable_block W484, W164a
end

//////////////////////////////////////////////////////////////////////////////
//  Pick-up the correct adder result  
//   
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, optimized by synthesizer.
// spyglass disable_block STARC05-2.8.1.3 
always @*
begin : agu_mux_adder_PROC
  casez ({x1_src2_sh1_r, x1_src2_sh2_r})
  2'b1z:   agu_addr0 = agu_addr0_sh1;  // src2 shifted by 1
  2'bz1:   agu_addr0 = agu_addr0_sh2;  // src2 shifted by 2
  default: agu_addr0 = agu_addr0_sh0;  // no src2 shift
  endcase 
  
  casez ({x1_src2_sh1_r, x1_src2_sh2_r})
  2'b1z:   agu_addr1 = agu_addr1_sh1;   // src2 shifted by 1
  2'bz1:   agu_addr1 = agu_addr1_sh2;   // src2 shifted by 2
  default: agu_addr1 = agu_addr1_sh0;   // no src2 shift
  endcase 
end

//////////////////////////////////////////////////////////////////////////////
//  Pick-up the correct bank sel  
//   
//////////////////////////////////////////////////////////////////////////////
always @*
begin : agu_mux_bsel_PROC
  casez ({x1_src2_sh1_r, x1_src2_sh2_r})
  2'b1z:   
  begin
    agu_bank_sel_lo = {x1_bank_sel_sh1[2], x1_bank_sel_sh1[0]};
    agu_bank_sel_hi = {x1_bank_sel_sh1[3], x1_bank_sel_sh1[1]};
  end  
  2'bz1:   
  begin
    agu_bank_sel_lo = {x1_bank_sel_sh2[2], x1_bank_sel_sh2[0]}; 
    agu_bank_sel_hi = {x1_bank_sel_sh2[3], x1_bank_sel_sh2[1]}; 
  end  
  default: 
  begin
    agu_bank_sel_lo = {x1_bank_sel_sh0[2], x1_bank_sel_sh0[0]}; 
    agu_bank_sel_hi = {x1_bank_sel_sh0[3], x1_bank_sel_sh0[1]}; 
  end  
  endcase
end
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3 
//////////////////////////////////////////////////////////////////////////////
//  Pick-up the correct lower part of the address for the bank sel 
//   
//////////////////////////////////////////////////////////////////////////////
always @*
begin : agu_mux_shft_PROC
  // The x1_mem_addr0 to the DMP depends on the addressing
  // mode, and shall be the computed AGU result agu_addr0 unless a pre-update
  // addressing mode is used, in which case agu_src1 shall be used.
  // Furthermore, when performing an EX instruction, the memory address is
  // given by the second source operand (this is indicated by the ucode bit
  // x1_mov_op_r being set). Thus, x1_base_addr is first selected from the
  // two AGU source values, and then the memory address is selected from 
  // either the base address or the computed address.
  //
  case ({x1_pre_addr_r, x1_mov_op_r})
  2'b10:  
  begin
    agu_src1_sh0 = agu_src1[3:0];
    agu_src2_sh0 = 4'b0000;
  end 
  
  2'b11: 
  begin
    agu_src1_sh0 = 4'b0000;
    agu_src2_sh0 = agu_src2[3:0];
  end  
  
  default: 
  begin
    agu_src1_sh0 = agu_src1[3:0];
    agu_src2_sh0 = agu_src2_addr0_sh0[3:0];
  end
  endcase  
end


//////////////////////////////////////////////////////////////////////////////
// Module instantiation  
//   
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_agu_bank_sel u_alb_agu_bank_sel_0 (
  .x1_byte_size_r         (x1_byte_size_r        ), 
  .x1_half_size_r         (x1_half_size_r        ), 
  .x1_double_size_r       (x1_double_size_r      ),
  .x1_src1                (agu_src1_sh0          ),
  .x1_src2                (agu_src2_sh0          ),

  .x1_bank_sel            (x1_bank_sel_sh0       )
);

npuarc_alb_agu_bank_sel u_alb_agu_bank_sel_1 (
  .x1_byte_size_r         (x1_byte_size_r         ),   
  .x1_half_size_r         (x1_half_size_r         ),   
  .x1_double_size_r       (x1_double_size_r       ),
  .x1_src1                (agu_src1[3:0]          ),
  .x1_src2                (agu_src2_addr0_sh1[3:0]),

  .x1_bank_sel            (x1_bank_sel_sh1        )
);

npuarc_alb_agu_bank_sel u_alb_agu_bank_sel_2 (
  .x1_byte_size_r         (x1_byte_size_r         ), 
  .x1_half_size_r         (x1_half_size_r         ), 
  .x1_double_size_r       (x1_double_size_r       ),
  .x1_src1                (agu_src1[3:0]          ),
  .x1_src2                (agu_src2_addr0_sh2[3:0]),

  .x1_bank_sel            (x1_bank_sel_sh2        )
);


endmodule // alb_agu
