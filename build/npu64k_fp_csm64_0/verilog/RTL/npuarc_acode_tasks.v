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
//    #      #####   #######  ######   #######
//   # #    #     #  #     #  #     #  #
//  #   #   #        #     #  #     #  #
// #     #  #        #     #  #     #  #####
// #######  #        #     #  #     #  #
// #     #  #     #  #     #  #     #  #
// #     #   #####   #######  ######   #######  #####
//
//
//     #######     #      #####   #    #   #####
//        #       # #    #     #  #   #   #     #
//        #      #   #   #        #  #    #
//        #     #     #   #####   ###      #####
//        #     #######        #  #  #          #
//        #     #     #  #     #  #   #   #     #
//        #     #     #   #####   #    #   #####
//
// ===========================================================================
//
// Description:
//
//  This file implements a set of instruction decode tasks for the
//  ARCompact instruction set. This file is included by decode.v which
//  references the tasks defined in this file.
//
//  The keyword ENH is used in comments to indicate where an enhancement to
//  the basecase functionality could be implemented in the future.
//
// ===========================================================================

// Definitions for all decode-related constants
//
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2012 Synopsys, Inc. All rights reserved.
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
// ######   #######   #####   #######  ######   #######         
// #     #  #        #     #  #     #  #     #  #               
// #     #  #        #        #     #  #     #  #               
// #     #  #####    #        #     #  #     #  #####           
// #     #  #        #        #     #  #     #  #               
// #     #  #        #     #  #     #  #     #  #               
// ######   #######   #####   #######  ######   #######  #####  
//
//
//  #####   #######  #     #   #####   #######  
// #     #  #     #  ##    #  #     #     #     
// #        #     #  # #   #  #           #     
// #        #     #  #  #  #   #####      #     
// #        #     #  #   # #        #     #     
// #     #  #     #  #    ##  #     #     #     
//  #####   #######  #     #   #####      #     
//
// ===========================================================================
//
// Description:
//
//  This file defines all the constants used to perform instruction
//  decode for the ARCompact instruction set.
//
// ===========================================================================

// There are 32 major opcode groups, each of which is identified by a
// 5-bit field. The following `defines give names to each of these.









// There are four main operand formats in the 0x04
// group of instructions. These are listed below.
//

// The 0x04 group of instruction contains the following
// dual operand instructions (mov is an exception!)
//

// The compare-branch instructions are listed
// below, together with their opcodes.
//

// The encodings of relational operator or bit tests for
// each of the BRcc, BBITn and SETcc instructions are given below.
//

// All single-operand 32-bit opcodes
//

// All zero-operand instructions
//

//////////////////////////////////////////////////////////////////////////////
// Extension opcodes and instruction formats
//////////////////////////////////////////////////////////////////////////////

// Barrel shift operations are encoded in GRP_ARC_EXT0_32
// and are dual operand instructions
//

// 64-bit multiplier operations are encoded in GRP_ARC_EXT0_32
// and are dual operand instructions
// [DEPRECATED in ARC 6000]
//

// Extension byte operations is encoded in GRP_ARC_EXT0_32
// and are all single operand instructions.
// These four operations are included under the SWAP_OPTION
//

// Extension byte operations is encoded in GRP_ARC_EXT0_32
// and are all single operand instructions.
// These six operations are included under the SHIFT_ASSIST
// configuration option, when SWAP_OPTION is also enabled.
//

// NORM operations are encoded in GRP_ARC_EXT0_32
// and are single operand instructions
//

// Extended arithmetic operations are encoded in GRP_ARC_EXT0_32
// [DEPRECATED in ARC 6000: ADDSDW_OP, SUBSDW_OP]
//
// dual operand extended-arith instructions
//

// single operand extended-arith instructions
//

// DSP operations are encoded in GRP_ARC_EXT0_32
//
// dual operand DSP instructions
// [DEPRECATED in ARC 6000]
//

// single operand DSP instructions
// [DEPRECATED in ARC 6000]
//

// Multiplication operations are encoded in GRP_BASECASE_32
// and are dual operand instructions
//

// SETcc opcodes are encoded in the GRP_BASECASE_32 and are
// all dual operand instructions
//

// DIV, DIVU, REM, REMU operations are encoded in GRP_ARC_EXT0_32
// These currently reuse the opcodes of DIVAW, MUL64 and MULU64, 
// which are not included in the ARC 6000 ISA.
//

// MAC, vector MPY/MAC, and vector ADD/SUB operations are
// encoded in GRP_ARC_EXT0_32, using opcodes 0x0E-0x1D and
// 0x30-0x3F.
//
// -- enabled when MPY_OPTION > 6
// -- enabled when MPY_OPTION > 7
// -- enabled when MPY_OPTION > 8

// Some DSP instructions are encoded in GRP_ARC_EXT0_32, 
// and are additional to MPY_OPTION8/9

// Some DSP instructions are encoded in GRP_ARC_EXT1_32


// FPU dual-operand (DOP format), single-precision instruction opcodes
//
//
// FPU single-operand (SOP format), single-precision instruction opcodes
//

// FPU dual-operand (DOP format), double-precision instruction opcodes
//
//
// FPU single-operand (SOP format), single-precision instruction opcodes
//


//////////////////////////////////////////////////////////////////////////////
// Auxiliary register addresses for base-case aux. registers
//////////////////////////////////////////////////////////////////////////////
//

//
// Non-standard cache control register





//
// 32'h00000060 - 32'h0000007F = Build Configuration Registers (read only)
//

//
// 32'h00000080 - 32'h0000009E = XY Memory Registers
//

//
// 32'h000000C0 - 32'h000000FF = Build Configuration Registers (read only)
//

// Aux registers above the base set
//

// 32'h00000103 - 32'h0000011F = Reserved
// 32'h00000120 - 32'h0000013F = Reserved
// 32'h00000140 - 32'h000001FF = Reserved


// 32'h00000202 - 32'h0000021F = Reserved
// 32'h00000220 - 32'h00000237 = AP_A* (actionpoints)
// 32'h00000238 - 32'h000003FF = Reserved


// Optional extension auxiliary registers


// MMU Build Configuration Registers (BCRs)
//
//
// MMU Maintenance and Control Registers
//

// Floating-point extension auxiliary registers
//

// Configuration-dependent macro definitions
//




`deflines inst_err_task_m;
begin
  // raise an Illegal Instruction exception
  illegal_instr = 1'b1;
end
`enddeflines

`deflines not_basecase_task_m;
begin
  // will be an illegal inst, unless EIA instruction matches
  av2_inst = 1'b0;
end
`enddeflines


`deflines init_local_regs_task_m;
begin
  flag_enable     = 1'b0;
  av2_inst        = 1'b0; // set when decoder matches an instruction
  illegal_operand = 1'b0; // set when decoder finds an illegal operand encoding
  illegal_instr   = 1'b0; // set when decoder finds an illegal instruction encoding
  z_write         = 1'b0;
  n_write         = 1'b0;
  c_write         = 1'b0;
  v_write         = 1'b0;
  limm_r0         = pre_limm_r0;
  limm_r1         = pre_limm_r1;
  rf_ra0          = pre_rf_ra0;
  rf_ra1          = pre_rf_ra1;
  rf_renb0        = pre_rf_renb0;
  rf_renb1        = pre_rf_renb1;
  rf_renb0_64     = pre_rf_renb0_64;
  rf_renb1_64     = pre_rf_renb1_64;
  opds_in_sa      = eia_inst_valid;
  kernel_op       = eia_kernel;
end
`enddeflines

`deflines flag_enable_task_m;
begin
  z_wen = z_write & flag_enable;
  n_wen = n_write & flag_enable;
  c_wen = c_write & flag_enable;
  v_wen = v_write & flag_enable;
end
`enddeflines


`deflines f_bit_task_m;
begin
  flag_enable = inst[15];
end
`enddeflines


`deflines has_limm_task_m;
begin
  has_limm = limm_r0 | limm_r1;
end
`enddeflines

//////////////////////////////////////////////////////////////////////////////
// ------------------------------ EC5 ONLY -------------------------------- //
//                                                                          //
// To simplify decoding, and improve critical path timing, the w0_lpc       //
// signal is asserted whenever there is an address on write-port 0 which is //
// greater than or equal to 32. This signal is only used to stall the Fetch //
// stage in case of RAW hazard with LP_COUNT and a loop-closing PC value    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines writes_lp_count_task_m;
begin
  wa0_lpc = rf_wenb0 & (rf_wa0 == 6'd60);
end
`enddeflines

`deflines illegal_operands_task_m;
begin
  //////////////////////////////////////////////////////////////////////////////
  //                                                                          //
  // This task detects illegal register operand usage. The following table    //
  // indicates the legal (OK) cases, the illegal (x) cases, the cases where   //
  // it is legal if the register defined by EIA and readable (EIA-R) or       //
  // writable (EIA-W).                                                        //
  //                                                                          //
  //   Register  Number  Read     Write(0)   Write(1)                         //
  //   ---------------------------------------------                          //
  //   ACCL       58     OK         OK        OK                              //
  //   ACCH       59     OK         OK        OK                              //
  //   PCL        63     OK          x         x                              //
  //   LIMM       62      x          x         x                              //
  //   RESERVED   61      x          x         x                              //
  //   LP_COUNT   60     OK     1-cycle only   x                              //
  //   ---------------------------------------------                          //
  //   extension  59     EIA-R      EIA-W      x                              //
  //      core    :      EIA-R      EIA-W      x                              //
  //    registers 32     EIA-R      EIA-W      x                              //
  //   ---------------------------------------------                          //
  //   baseline  31      OK          OK       OK                              //
  //     core     :      OK          OK       OK                              //
  //   registers  0      OK          OK       OK                              //
  //   ---------------------------------------------                          //
  //                                                                          //
  //  When EIA extensions are defined, the HAS_EIA macro will be set to 1.    //
  //  If the read register addresses, rf_ra0 (resp. rf_ra1), select an EIA    //
  //  extension core register, and if those registers are readable, then      //
  //  the eia_ra0_is_ext (resp. eia_ra1_is_ext) will be asserted. In this     //
  //  case, a read from that register is permitted.                           //
  //  If the write port 0 register address, rf_wa0, selects an EIA extension  //
  //  core register, and that register has write permission, then the signal  //
  //  eia_wa0_is_ext will be asserted.                                        //
  //                                                                          //
  //  Loads are not permitted to target an extension core register.           //
  //                                                                          //
  //  Any attempt to access an extension core register in User mode, when     //
  //  XPU bit for tht extension is not set, will raise a Privilege Violation  //
  //  exception. The logic for that is contained elsewhere.                   //
  //                                                                          //
  //  All writes to PCL, LIMM and the RESERVED register (r61) are illegal     //
  //  except within the context of a uop instruction.                         //
  //                                                                          //
  //  Values may only be written to LP_COUNT using 'fast' operations.         //
  //  Fast operations include all instructions except Loads, Multiply and     //
  //  Divide operations, and multi-cycle extension instructions.              //
  //                                                                          //
  //////////////////////////////////////////////////////////////////////////////

  invalid_instr   = illegal_instr
                  | (   (~uop_valid_r)
                      & (~av2_inst)
                      & (~eia_inst_valid)
                  )
                  | eia_illegal_cond
                  | (inst[15] & vector_op)
                  ;
                
  illegal_operand = illegal_operand |
                    (   rf_renb0                   // read port 0 is enabled and
                      & rf_ra0[5]                  // register is one of r32-r63
                      & (~( (rf_ra0[4:0] == 5'h1f) // but is neither PCL (r63)
                           |(rf_ra0[4:0] == 5'h1c) // nor LP_COUNT (r60)
                           | eia_ra0_is_ext        // nor a defined extension
                           |(rf_ra0[4:1] == 4'hd)  // register is ACCL or ACCH
                          )
                        )
                    )
                  | (   rf_renb1                   // read port 1 is enabled and
                      & rf_ra1[5]                  // register is one of r32-r63
                      & (~( (rf_ra1[4:0] == 5'h1f) // but is neither PCL (r63)
                           |(rf_ra1[4:0] == 5'h1c) // nor LP_COUNT (r60)
  // UOP PROL RA1 Reg 55, 56, 57, 61 allowed
                           |uop_valid_r
                           & ( (rf_ra1[4:0] == 5'h1d) // nor STATUS32 (r61)
                              |(rf_ra1[4:0] == 5'h17) // nor JLI_BASE (r55)
                              |(rf_ra1[4:0] == 5'h18) // nor LDI_BASE (r56)
                              |(rf_ra1[4:0] == 5'h19) // nor EI_BASE  (r57)
                              |(rf_ra1[4:0] == 5'h1A) // nor LP_START (r58)
                              |(rf_ra1[4:0] == 5'h1B) // nor LP_END   (r59)
                              |(rf_ra1[4:0] == 5'h1c) // nor LP_COUNT (r60)
                            )
                           | eia_ra1_is_ext        // nor a defined extension
                           |(rf_ra1[4:1] == 4'hd)  // register is ACCL or ACCH
                          )
                        )
                    )
                  |     rf_wenb1 
                      & (rf_wa1 [5:0] == 6'h3c)
                      & (~uop_valid_r)
                      & (
                          lr_op
                        | load
                        | mpy_op
                        | vector_op
                        | div_op
                        | (eia_inst_valid & eia_multi_cycle)
                        )
                  | (   rf_wenb0
                      & rf_wa0[5]
                      & (   (   (rf_wa0[4:2] == 3'd7)
                              & (   rf_wa0[0]
                                  | rf_wa0[1]
                                  | lr_op
                                  | mpy_op
                                  | vector_op
                                  | div_op
                                  | (eia_inst_valid & eia_multi_cycle)
                               )
                            )
                          | (   (rf_wa0[4:2] != 3'd7)
                              & (~eia_wa0_is_ext)
                              & (rf_wa0[4:1] != 4'hd) // register is not ACCL or ACCH
                            )
                        )
                    )
                  | (   rf_wenb1
                      & rf_wa1[5]
                      & (   (   (rf_wa1[4:2] == 3'h7)
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h1C)) // LP_COUNT (r60)
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h1d)) // Status32 (r61)
                            )
                          | (   (rf_wa1[4:2] != 3'h7)
                              & (~eia_wa1_is_ext)
                              & (rf_wa1[4:1] != 4'hd) // register is not ACCL or ACCH
  // UOP EPIL RA1 Reg 55, 56, 57, 61 allowed
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h17)) // nor JLI_BASE (r55)
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h18)) // nor LDI_BASE (r56)
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h19)) // nor EI_BASE  (r57)
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h1A)) // nor LP_START (r58)
                              & ((~uop_valid_r) | (rf_wa1[4:0] != 5'h1B)) // nor LP_END   (r59)
                            )
                        )
                    )
                  | (rf_renb0_64 & rf_ra0[0])
                  | (rf_renb0_64 & (rf_ra0[5:1] == 5'h1e))  // r60 as reg-pair
                  | (rf_renb1_64 & rf_ra1[0])               // odd register
                  | (rf_renb1_64 & (rf_ra1[5:1] == 5'h1e))  // r60 as reg-pair
                  | (rf_wenb0_64 & rf_wa0[0])
                  | (rf_wenb1_64 & rf_wa1[0])
                  | (eia_illegal_cr_access & (!uop_valid_r))
                  ;
end
`enddeflines


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Register and short-immediate operand extraction tasks, which also set    //
// the register field enable signals and detect a long-immediate operand.   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines regs_a_32_task_m;
begin
  // Extract field 'a' from a 32-bit inst where
  // 'a' is destination of non-Load operation
  rf_wa0 = inst[5:0];
  rf_wenb0 = (inst[5:0] != 6'd62);
end
`enddeflines


`deflines regs_a1_32_task_m;
begin
  // Extract field 'a' from a 32-bit inst
  // where 'a' is destination of a Load operation
  rf_wa1 = inst[5:0];
  rf_wenb1 = (inst[5:0] != 6'd62);
end
`enddeflines


`deflines regs_c_32_task_m;
begin                     // EC5 requires that J or JL also sets opd3_sel
end
`enddeflines


`deflines regs_s12_32_task_m;
begin
  shimm     = { {20{inst[5]}}, inst[5:0], inst[11:6] };
  sel_shimm = 1'b1;
end
`enddeflines


`deflines regs_u6_32_task_m;
begin                     // source operand only
  shimm     = { 26'd0, inst[11:6] };
  sel_shimm = 1'b1;
end
`enddeflines

`deflines regs_bu6_32_task_m;
begin                     // for source operands only
  `npuarc_regs_u6_32_task_m;
end
`enddeflines


`deflines regs_q_32_task_m;
begin
  q_field   = inst[4:0];
end
`enddeflines


`deflines regs_b_32_task_m;
begin
end
`enddeflines


`deflines regs_bbq_32_task_m;
begin
  rf_wa0   = { inst[14:12], inst[26:24] };
  rf_wenb0 = ({ inst[14:12], inst[26:24] } != 6'd62);

  `npuarc_regs_bq_32_task_m;
end
`enddeflines


`deflines regs_bq_32_task_m;
begin                     // for source operands only
  `npuarc_regs_b_32_task_m;
  `npuarc_regs_q_32_task_m;
  `npuarc_f_bit_task_m;
end
`enddeflines


`deflines regs_bc_32_task_m;
begin
  `npuarc_regs_b_32_task_m;

end
`enddeflines


`deflines regs_abc_32_task_m;
begin
  `npuarc_regs_a_32_task_m;
  `npuarc_regs_bc_32_task_m;
  `npuarc_f_bit_task_m;
end
`enddeflines


`deflines regs_a1bc_32_task_m;
begin                     // where operation is a Load writing to write port 1
  `npuarc_regs_a1_32_task_m;
  `npuarc_regs_bc_32_task_m;
  `npuarc_f_bit_task_m;
end
`enddeflines


`deflines regs_mov_bs12_task_m;
begin
  rf_wa0    = { inst[14:12], inst[26:24] };
  rf_wenb0  = ({ inst[14:12], inst[26:24] } != 6'd62);
  `npuarc_regs_s12_32_task_m;
  `npuarc_f_bit_task_m;
end
`enddeflines

`deflines regs_bs12_32_task_m;
begin
  `npuarc_regs_s12_32_task_m;
  `npuarc_f_bit_task_m;
end
`enddeflines

`deflines regs_bbs12_32_task_m;
begin                       // as well as field 's12' from a 32-bit inst.
  rf_wa0    = { inst[14:12], inst[26:24] };
  rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
  `npuarc_regs_bs12_32_task_m;
end
`enddeflines

`deflines regs_sop_bc_32_task_m;
begin
  rf_wa0    = { inst[14:12], inst[26:24] };
  rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
  `npuarc_f_bit_task_m;
end
`enddeflines


`deflines regs_sop_bu6_32_task_m;
begin
  rf_wa0    = { inst[14:12], inst[26:24] };
  rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
  shimm     = { 26'd0, inst[11:6] };
  sel_shimm = 1'b1;
  `npuarc_f_bit_task_m;
end
`enddeflines


`deflines regs_abu6_32_task_m;
begin
  `npuarc_regs_a_32_task_m;
  `npuarc_regs_bu6_32_task_m;
  `npuarc_f_bit_task_m;
end
`enddeflines

`deflines regs_mov_bc_32_task_m;
begin
  rf_wa0        = { inst[14:12], inst[26:24] };
  rf_wenb0      = ({inst[14:12], inst[26:24]} != 6'd62);
end
`enddeflines

`deflines regs_mov_bu6_32_task_m;
begin
  rf_wa0    = { inst[14:12], inst[26:24] };
  rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
  shimm     = { 26'd0, inst[11:6] };
  sel_shimm = 1'b1;
end
`enddeflines


`deflines regs_lpcc_s12_task_m;
begin
  offset = { {19{inst[5]}}, inst[5:0], inst[11:6], 1'd0 };
end
`enddeflines

`deflines regs_lp_u6_task_m;
begin
  offset  = { 25'd0, inst[11:6], 1'd0 };
end
`enddeflines

`deflines regs_lpcc_u6q_task_m;
begin
  offset  = { 25'd0, inst[11:6], 1'd0 };
  `npuarc_regs_q_32_task_m;
  illegal_instr = !inst[5];
end
`enddeflines


`deflines regs_b_dest_16_task_m;
begin
  rf_wa0   = { 2'b00, inst[26], inst[26:24] };
  rf_wenb0 = 1'b1;
end
`enddeflines

`deflines regs_b_ld_dest_16_task_m;
begin
  rf_wa1   = { 2'b00, inst[26], inst[26:24] };
  rf_wenb1 = 1'b1;
end
`enddeflines

// Used only by load instructions
//
`deflines regs_c_dest_16_task_m;
begin
  rf_wa1   = { 2'b00, inst[23], inst[23:21] };
  rf_wenb1 = 1'b1;
end
`enddeflines


`deflines regs_b_src1_16_task_m;
begin
end
`enddeflines


`deflines regs_b_src2_16_task_m;
begin
end
`enddeflines


`deflines regs_c_src2_16_task_m;
begin
end
`enddeflines


`deflines regs_bbc_16_task_m;
begin
  `npuarc_regs_b_dest_16_task_m;
  `npuarc_regs_b_src1_16_task_m;
  `npuarc_regs_c_src2_16_task_m;
end
`enddeflines

`deflines regs_bc_16_sop_task_m;
begin
  `npuarc_regs_b_dest_16_task_m;
  `npuarc_regs_c_src2_16_task_m;
end
`enddeflines


`deflines regs_a_16_task_m;
begin
  rf_wa0 = { 2'b00, inst[18], inst[18:16] };
  rf_wenb0 = 1'b1;
end
`enddeflines

`deflines regs_a1_16_task_m;
begin
  rf_wa1 = { 2'b00, inst[18], inst[18:16] };
  rf_wenb1 = 1'b1;
end
`enddeflines

`deflines regs_bc_16_task_m;
begin
end
`enddeflines

`deflines regs_cbu3_16_task_m;
begin
  rf_wa0 = { 2'b00, inst[23], inst[23:21] };
  rf_wenb0 = 1'b1;
  shimm  = { 29'd0, inst[18:16] };
  sel_shimm = 1'b1;
end
`enddeflines


`deflines regs_bbh_16_task_m;
begin
  rf_wa0 = { 2'b00, inst[26], inst[26:24] };
  rf_wenb0 = 1'b1;
end
`enddeflines


`deflines regs_mov_hb_16_task_m;
begin
  rf_wa0 = { 1'b0, inst[17:16], inst[23:21] };
  rf_wenb0 = (rf_wa0[4:0] != 5'd30);
end
`enddeflines


`deflines regs_mov_bh_16_task_m;
begin
  rf_wa0 = { 2'b00, inst[26], inst[26:24] };
  rf_wenb0 = 1'b1;
end
`enddeflines


`deflines regs_bh_16_task_m;
begin
end
`enddeflines

`deflines shimm_s3_16_task_m;
begin
  shimm = { {29{&inst[26:24]}}, inst[26:24]};
  sel_shimm = 1'b1;
end
`enddeflines

`deflines regs_h_src1_16_task_m;
begin
end
`enddeflines

`deflines regs_h_dst_16_task_m;
begin
  rf_wa0   = { 1'b0, inst[17:16], inst[23:21] };
  rf_wenb0 = (rf_wa0[4:0] != 5'd30);
end
`enddeflines

`deflines regs_hhs3_16_task_m;
begin
  `npuarc_regs_h_dst_16_task_m;
  `npuarc_regs_h_src1_16_task_m;
  `npuarc_shimm_s3_16_task_m;
end
`enddeflines

`deflines regs_mov_hs3_16_task_m;
begin
  `npuarc_regs_h_dst_16_task_m;
  `npuarc_shimm_s3_16_task_m;
end
`enddeflines

`deflines regs_hs3_16_task_m;
begin
  `npuarc_regs_h_src1_16_task_m;
  `npuarc_shimm_s3_16_task_m;
end
`enddeflines

`deflines regs_h_src2_16_task_m;
begin
end
`enddeflines

`deflines regs_g_dst_16_task_m;
begin
  rf_wa0   = { 1'b0, inst[20:19], inst[26:24] };
  rf_wenb0 = (rf_wa0[4:0] != 5'd30);
end
`enddeflines

`deflines ld_rr_u5_16_task_m;
begin
  load = 1'b1;
  rf_wa1    = { 4'b0000, inst[25:24] };
  rf_wenb1  = 1'b1;
  shimm     = { 27'd0, inst[26], inst[20:19], 2'b00 };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines regs_a_dst_16_task_m;
begin
  rf_wa0   = { 2'b00, inst[18], inst[18:16] };
  rf_wenb0 = 1'b1;
end
`enddeflines

`deflines regs_ac_16_task_m;
begin
  `npuarc_regs_a_dst_16_task_m;
  `npuarc_regs_c_src2_16_task_m;
end
`enddeflines

`deflines ld_as_16_task_m;
begin
  av2_inst  = 1'b1;
  load      = 1'b1;
  src2_sh2  = 1'b1;
  rf_wa1    = { 2'b00, inst[18], inst[18:16] };
  rf_wenb1  = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines add_r01_u6_task_m;
begin
  av2_inst  = 1'b1;
  rf_wa0    = { 5'b00000, inst[23] };
  rf_wenb0  = 1'b1;
  shimm     = { 26'd0, inst[22:20], inst[18:16] };
  sel_shimm = 1'b1; 
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines mem_r01_gp_s9_task_m;
begin
  av2_inst  = 1'b1;
  rf_wa1    = 6'd1;    // load data into R1
  rf_wenb1  = ~inst[20];
  load      = ~inst[20];
  store     =  inst[20];
  shimm     = { {23{inst[26]}}, inst[26:21], inst[18:16] };
  sel_shimm = 1'b1; 
  src2_sh2  = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines ldi_s_task_m;
begin
  av2_inst   = 1'b1;
  `npuarc_regs_b_ld_dest_16_task_m;
  load       = 1'b1;
  ldi_src0   = 1'b1; // select LDI_BASE aux register as src0
  shimm      = { 25'd0, inst[23:20], inst[18:16] };
  sel_shimm  = 1'b1;
  src2_sh2   = 1'b1; // table index is always scaled by 4
end
`enddeflines

`deflines ldi_task_m;
begin
  av2_inst   = 1'b1;
  load       = 1'b1;
  ldi_src0   = 1'b1; // select LDI_BASE aux register as src0
  src2_sh2   = 1'b1; // table index is always scaled by 4
  rf_wa1     = { inst[14:12], inst[26:24] };
  rf_wenb1   = ({inst[14:12], inst[26:24]} != 6'd62);
end
`enddeflines

`deflines ei_s_task_m;
begin
  av2_inst       = 1'b1;
  `npuarc_grp_b_target_task_m;
  ei_op          = 1'b1;
end
`enddeflines


`deflines regs_bbu5_16_task_m;
begin
  rf_wa0    = { 2'b00, inst[26], inst[26:24] };
  rf_wenb0  = 1'b1;
  shimm     = { 27'd0, inst[20:16] };
  sel_shimm = 1'b1;
end
`enddeflines


`deflines regs_bu7_16_task_m;
begin
  shimm     = { 25'd0, inst[22:16] };
  sel_shimm = 1'b1;
end
`enddeflines


`deflines regs_bbu7_16_task_m;
begin
  rf_wa0   = { 2'b00, inst[26], inst[26:24] };
  rf_wenb0 = 1'b1;
  `npuarc_regs_bu7_16_task_m;
end
`enddeflines


`deflines regs_push_pop_16_task_m;
begin

  rf_wenb0  = 1'b1;
  rf_wa0    = 6'd28;
end
`enddeflines

`deflines pop_16_task_m;
begin
  av2_inst  = 1'b1;
  `npuarc_regs_push_pop_16_task_m;
  sel_shimm = 1'b1;
  shimm     = 32'd4;
  `npuarc_add_16_task_m;
  pre_addr  = 1'b1;
  load = 1'b1;
  rf_wenb1  = 1'b1;
  if ( inst[20:16] == 5'd1 )
    rf_wa1  = { 2'd0, inst[26], inst[26:24] };
  else if (inst[20:16] == 5'd17)
    rf_wa1  = 6'd31;         // BLINK register
  else
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines push_16_task_m;
begin
  av2_inst  = 1'b1;
  `npuarc_regs_push_pop_16_task_m;
  sel_shimm = 1'b1;
  shimm     = 32'hfffffffc;
  `npuarc_add_16_task_m;
  store     = 1'b1;
  opd3_sel  = 1'b1;
  if (( inst[20:16] != 5'd1 ) && (inst[20:16] != 5'd17))
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines uop_opd_task_m;
begin
  // check for u[3:0] == 1111, this  is a  illegal operand
  //
  if (inst[20:17] == 4'b1111)
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines enter_s_task_m;
begin
  av2_inst = 1'b1;
  `npuarc_uop_opd_task_m;
  multi_op = |{ inst[26:24], inst[20:17] };
  enter_op = |{ inst[26:24], inst[20:17] };
  if (inst[26] == 1'b1)   // enter_s must have bit 10 = 0
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines leave_s_task_m;
begin
  av2_inst = 1'b1;
  `npuarc_uop_opd_task_m;
  multi_op = |{ inst[26:24], inst[20:17] };
  leave_op = |{ inst[26:24], inst[20:17] };
end
`enddeflines

`deflines zero_operand_task_m;
begin
  rf_wenb0 = 1'b0;
end
`enddeflines

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Two-operand ALU function micro-code tasks                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines add_task_m;
begin
  av2_inst = 1'b1;
  add_op  = 1'b1;         // perform 2'c complement addition
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
end
`enddeflines

`deflines add_16_task_m;
begin
  av2_inst = 1'b1;
  add_op  = 1'b1;         // perform 2'c complement addition
  fast_op = 1'b1;         // allow next-cycle forwarding of result
end
`enddeflines

`deflines adc_task_m;
begin
  av2_inst = 1'b1;
  add_op  = 1'b1;         // perform 2'c complement addition
  with_carry = 1'b1;      // include FLAGS.C bit in sum
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force instruction to execute at X1
end
`enddeflines

`deflines sub_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute A + ~B + 1
  inv_src2 = 1'b1;        // select ~B as src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
end
`enddeflines

`deflines sub_16_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute A + ~B + 1
  inv_src2 = 1'b1;        // select ~B as src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
end
`enddeflines

`deflines sbc_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  with_carry = 1'b1;      // compute A + ~B + ~FLAG.C
  inv_src2 = 1'b1;        // select ~B as src2 and ~FLAG.C as Cin
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force instruction to execute at X1
end
`enddeflines

`deflines and_task_m;
begin
  av2_inst = 1'b1;
  and_op = 1'b1;          // perform dst = src1 & src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines or_task_m;
begin
  av2_inst = 1'b1;
  or_op = 1'b1;           // perform logical OR
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines xor_task_m;
begin
  av2_inst = 1'b1;
  xor_op = 1'b1;          // perform logical AND
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines abs_task_m;
begin
  av2_inst   = 1'b1;
  add_op     = 1'b1;      // perform 2'c complement subtraction
  force_cin  = 1'b1;      // compute 0 + ~B + 1
  inv_src2   = 1'b1;      // select ~B as src2
  abs_op     = 1'b1;      // enable abs logic to select src2 or 0-src2
  slow_op    = 1'b1;      // two-cycle latency in ARCv2HS
  opds_in_sa = 1'b1;      // force execution in early ALU
  c_write    = 1'b1;      // sets C to result[31]
  z_write    = 1'b1;      // set Z if result is zero
  n_write    = 1'b1;      // set N to result[31]
  v_write    = 1'b1;      // set V if src2 == 0x8000_0000
end
`enddeflines

`deflines min_task_m;
begin
  av2_inst   = 1'b1;
  add_op     = 1'b1;      // perform 2'c complement subtraction
  force_cin  = 1'b1;      // compute A + ~B + 1
  inv_src2   = 1'b1;      // select ~B as src2
  min_op     = 1'b1;      // enable min logic to select src1 or src2
  slow_op    = 1'b1;      // two-cycle latency in ARCv2HS
  opds_in_sa = 1'b1;      // force execution in early ALU
  c_write    = 1'b1;      // C flag <= 1 if src2 selected
  z_write    = 1'b1;
  n_write    = 1'b1;
  v_write    = 1'b1;
end
`enddeflines

`deflines max_task_m;
begin
  av2_inst   = 1'b1;
  add_op     = 1'b1;      // perform 2'c complement subtraction
  force_cin  = 1'b1;      // compute ~A + B + 1
  inv_src2   = 1'b1;      // select ~A as src2
  max_op     = 1'b1;      // enable max logic to select src1 or src2
  slow_op    = 1'b1;      // two-cycle latency in ARCv2HS
  opds_in_sa = 1'b1;      // force execution in early ALU
  c_write    = 1'b1;      // C flag <= 1 if src2 selected
  z_write    = 1'b1;
  n_write    = 1'b1;
  v_write    = 1'b1;
end
`enddeflines

`deflines bic_task_m;
begin
  av2_inst = 1'b1;
  and_op   = 1'b1;        // perform dst = src1 & ~src2
  fast_op  = 1'b1;        // allow next-cycle forwarding of result
  inv_src2 = 1'b1;
  z_write  = 1'b1;
  n_write  = 1'b1;
end
`enddeflines

`deflines mov_task_m;
begin
  av2_inst = 1'b1;
  mov_op   = 1'b1;        // MOV src2 to dst
  fast_op  = 1'b1;        // allow next-cycle forwarding of result
  `npuarc_f_bit_task_m;          // detect mov.f instruction
  z_write  = 1'b1;        //  - enable Z update if mov.f
  n_write  = 1'b1;        //  - enable N update if mov.f
end
`enddeflines

`deflines mov_s_task_m;
begin
  av2_inst = 1'b1;
  mov_op   = 1'b1;        // MOV src2 to dst
  fast_op  = 1'b1;        // allow next-cycle forwarding of result
end
`enddeflines

`deflines mov_s_ne_task_m;
begin
  av2_inst = 1'b1;
  mov_op   = 1'b1;        // MOV src2 to dst
  fast_op  = 1'b1;        // allow next-cycle forwarding of result
  q_field  = 5'b00010;    // Conditional on .ne
end
`enddeflines

`deflines tst_task_m;
begin
  av2_inst = 1'b1;
  rf_wenb0 = 1'b0;        // disable destination write
  and_op = 1'b1;          // perform bit-wise AND
  z_write = 1'b1;
  n_write = 1'b1;
  flag_enable = 1'b1;     // tst and tst_s always update flags
  fast_op = 1'b1;         // flag result available after 1 cycle

  if (inst[15] == 1'b0)   // TST must have bit 15 set to 1
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines tst_s_task_m;
begin
  av2_inst = 1'b1;
  rf_wenb0 = 1'b0;        // disable destination write
  and_op = 1'b1;          // perform bit-wise AND
  z_write = 1'b1;
  n_write = 1'b1;
  flag_enable = 1'b1;     // tst and tst_s always update flags
  fast_op = 1'b1;         // flag result available after 1 cycle
end
`enddeflines

`deflines cmp_task_m;
begin
  av2_inst = 1'b1;
  rf_wenb0 = 1'b0;        // disable destination write
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute A + ~B + 1
  inv_src2 = 1'b1;        // select ~B as src2
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  flag_enable = 1'b1;
  fast_op = 1'b1;         // flag result available after 1 cycle
end
`enddeflines

`deflines rcmp_task_m;
begin
  av2_inst = 1'b1;
  rf_wenb0 = 1'b0;        // disable destination write
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute ~A + B + 1
  inv_src1 = 1'b1;        // select ~A as src2
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  flag_enable = 1'b1;
  fast_op = 1'b1;         // flag result available after 1 cycle
end
`enddeflines

`deflines rsub_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute ~A + B + 1
  inv_src1 = 1'b1;        // select ~A as src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
end
`enddeflines

`deflines dbnz_task_m;
begin
  av2_inst = 1'b1;
  // --- ucode to force src2 to be a short-immediate value 1 ---
  sel_shimm   = 1'b1;   // force selection of shimm as src2
  shimm       = 32'd1;  // set the value to 1.
  // --- ucode for SUB rb, rb, src2 ----------------------------
  add_op      = 1'b1;   // perform 2'c complement subtraction
  force_cin   = 1'b1;   // compute A + ~B + 1
  inv_src2    = 1'b1;   // select ~B as src2
  rf_wenb0    = 1'b1;   // enable destination write
  rf_wa0      = rf_ra0; // set up the destination address
  //
  // --- ucode for BRNE rb, src2, offset -----------------------    
  brcc_bbit   = 1'b1;   // select BRcc branch operation
  rel_branch  = 1'b1;   // select PC+offset as target
  offset      = { {19{inst[5]}}, inst[5:0], inst[11:6], 1'b0 };
  cc_field    = 3'h1;
  dslot       = inst[16];
  //
  // DBNZ instruction supports only REG-S12 format and does
  // not permit Rb to be the limm indicator. 
  //
  if ((inst[23:22] != 2'b10) || (limm_r1 == 1'b1))
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines bset_task_m;
begin
  av2_inst = 1'b1;
  or_op = 1'b1;           // perform logical OR
  bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  fast_op = 1'b1;         // flag result available after 1 cycle
end
`enddeflines

`deflines bclr_task_m;
begin
  av2_inst = 1'b1;
  and_op = 1'b1;          // perform logical AND
  bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  inv_src2 = 1'b1;        // invert src2 to mask out one bit only
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  fast_op = 1'b1;         // flag result available after 1 cycle
end
`enddeflines

`deflines btst_task_m;
begin
  av2_inst = 1'b1;
  and_op = 1'b1;          // perform logical AND
  bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  rf_wenb0 = 1'b0;        // disable writing to destination register
  flag_enable = 1'b1;     // btst and btst_s always update flags
  z_write = 1'b1;
  n_write = 1'b1;
  fast_op = 1'b1;         // flag result available after 1 cycle

  if (inst[15] == 1'b0)   // BTST must have bit 15 set to 1
    `npuarc_inst_err_task_m;
end
`enddeflines

`deflines btst_s_task_m;
begin
  av2_inst = 1'b1;
  and_op = 1'b1;          // perform logical AND
  bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  rf_wenb0 = 1'b0;        // disable writing to destination register
  flag_enable = 1'b1;     // btst and btst_s always update flags
  z_write = 1'b1;
  n_write = 1'b1;
  fast_op = 1'b1;         // flag result available after 1 cycle
end
`enddeflines

`deflines bxor_task_m;
begin
  av2_inst = 1'b1;
  xor_op = 1'b1;          // perform logical XOR
  bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines bmsk_task_m;
begin
  av2_inst = 1'b1;
  and_op = 1'b1;          // perform logical AND
  mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines bmskn_task_m;
begin
  av2_inst = 1'b1;
  and_op = 1'b1;          // perform logical AND
  mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  inv_src2 = 1'b1;        // invert the bit mask
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines add1_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement addition
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  src2_sh1 = 1'b1;        // shift src1 by one bit to the left
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines add2_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement addition
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  src2_sh2 = 1'b1;        // shift src2 by two bits to the left
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines add3_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement addition
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  src2_sh3 = 1'b1;        // shift src2 by three bits to the left
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines sub1_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute A + ~B + 1
  inv_src2 = 1'b1;        // select ~B as src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  src2_sh1 = 1'b1;        // shift src2 by one bit to the left
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines sub2_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute A + ~B + 1
  inv_src2 = 1'b1;        // select ~B as src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  src2_sh2 = 1'b1;        // shift src2 by two bits to the left
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines sub3_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;          // perform 2'c complement subtraction
  force_cin = 1'b1;       // compute A + ~B + 1
  inv_src2 = 1'b1;        // select ~B as src2
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  src2_sh3 = 1'b1;        // shift src2 by three bits to the left
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines sub_s_ne_task_m;
begin
  av2_inst = 1'b1;
  rf_wa0       = { 2'b00, inst[26], inst[26:24] };
  rf_wenb0     = 1'b1;    // enable write to [b]
  fast_op      = 1'b1;    // allow next-cycle forwarding of result
  mov_op       = 1'b1;    // sub_s.ne b,b,b => mov.ne b,0
  
  // q_field[4] is always 0 for non-extension instructions
  //
  q_field[3:0] = 4'b0010; // NE condition
end
`enddeflines

`deflines asl_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  left_shift = 1'b1;
  signed_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  v_write = 1'b1;
end
`enddeflines

`deflines asr_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  signed_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
end
`enddeflines

`deflines lsr_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
end
`enddeflines

`deflines rlc_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  left_shift = 1'b1;
  rotate_op = 1'b1;
  with_carry = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
end
`enddeflines

`deflines ror_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  rotate_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
end
`enddeflines

`deflines rol_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  rotate_op = 1'b1;
  left_shift = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
end
`enddeflines

`deflines rrc_task_m;
begin
  av2_inst = 1'b1;
  simple_shift_op = 1'b1; // select logic unit shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  rotate_op = 1'b1;
  with_carry = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
end
`enddeflines

`deflines aslm_task_m;
begin
  av2_inst = 1'b1;
  barrel_shift_op = 1'b1; // select barrel shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  signed_op = 1'b1;       // arithmetic shift
  left_shift = 1'b1;      // left shift
  z_write = 1'b1;
  n_write = 1'b1;
  c_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines lsrm_task_m;
begin
  av2_inst = 1'b1;
  barrel_shift_op = 1'b1; // select barrel shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;         // logical right shift by default
  n_write = 1'b1;
  c_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines asrm_task_m;
begin
  av2_inst = 1'b1;
  barrel_shift_op = 1'b1; // select barrel shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  signed_op = 1'b1;       // arithmetic shift
  z_write = 1'b1;         // right shift by default
  n_write = 1'b1;
  c_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines rorm_task_m;
begin
  av2_inst = 1'b1;
  barrel_shift_op = 1'b1; // select barrel shifter
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  rotate_op = 1'b1;       // rotate is selected
  z_write = 1'b1;         // right shift by default
  n_write = 1'b1;
  c_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines sexb_task_m;
begin
  av2_inst = 1'b1;
  mov_op = 1'b1;
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  byte_size = 1'b1;
  signed_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines sexw_task_m;
begin
  av2_inst = 1'b1;
  mov_op = 1'b1;
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  half_size = 1'b1;
  signed_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines extb_task_m;
begin
  av2_inst = 1'b1;
  mov_op = 1'b1;
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  byte_size = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines extw_task_m;
begin
  av2_inst = 1'b1;
  mov_op = 1'b1;
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  half_size = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines not_task_m;
begin
  av2_inst = 1'b1;
  xor_op = 1'b1;
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  inv_src1 = 1'b1;        // compute ~(0) ^ src
  z_write = 1'b1;
  n_write = 1'b1;
end
`enddeflines

`deflines neg_task_m;
begin
  av2_inst = 1'b1;
  add_op = 1'b1;
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  inv_src2 = 1'b1;        // compute 0 + ~src + 1
  force_cin = 1'b1;
end
`enddeflines

`deflines swap_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  half_size  = 1'b1;
  rotate_op  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines swape_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  rotate_op  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines lsl16_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  half_size  = 1'b1;
  left_shift = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines lsr16_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  half_size  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines asr16_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  signed_op  = 1'b1;
  half_size  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines asr8_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  signed_op  = 1'b1;
  byte_size  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines lsr8_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  byte_size  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines lsl8_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  byte_size  = 1'b1;
  left_shift = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines rol8_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  byte_size  = 1'b1;
  left_shift = 1'b1;
  rotate_op  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines ror8_task_m;
begin
  av2_inst = 1'b1;
  swap_op = 1'b1;
  fast_op = 1'b1;
  z_write = 1'b1;
  n_write = 1'b1;
  byte_size  = 1'b1;
  rotate_op  = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines xbfu_task_m;
begin
  av2_inst = 1'b1;
  barrel_shift_op = 1'b1; // select barrel shifter
  mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
  src2_mask_sel = 1'b1;   // select mask in operand stage
  fast_op = 1'b1;         // allow next-cycle forwarding of result
  z_write = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

//====================================================================
// The following four signals are used to control operations within
// the bitscan group, which includes NORM, NORMW, FFS and FLS
//
//  Instruction    norm_op    signed_op   half_size   byte_size
//  ------------------------------------------------------------
//     NORM          1            1          0            0
//     NORMW         1            1          1            0
//     FFS           1            0          0            0
//     FLS           1            0          0            1
//
//====================================================================

`deflines norm_task_m;
begin
  av2_inst = 1'b1;
  norm_op   = 1'b1;
  fast_op   = 1'b1;
  signed_op = 1'b1;
  z_write   = 1'b1;
  n_write   = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines


`deflines normw_task_m;
begin
  av2_inst  = 1'b1;
  norm_op   = 1'b1;
  fast_op   = 1'b1;
  signed_op = 1'b1;
  half_size = 1'b1;
  z_write   = 1'b1;
  n_write   = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines ffs_task_m;
begin
  av2_inst  = 1'b1;
  norm_op   = 1'b1;
  fast_op   = 1'b1;
  z_write   = 1'b1;
  n_write   = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines fls_task_m;
begin
  av2_inst  = 1'b1;
  norm_op   = 1'b1;
  fast_op   = 1'b1;
  byte_size = 1'b1;
  z_write   = 1'b1;
  n_write   = 1'b1;
  opds_in_sa = 1'b1;      // force execution in early ALU
end
`enddeflines

`deflines mpyw_task_m;
begin
  av2_inst = 1'b1;
   mpy_op     = 1'b1;
   half_size  = 1'b1;
   signed_op  = 1'b1;
   z_write    = 1'b1;
   n_write    = 1'b1;
   v_write    = 1'b1;
end
`enddeflines


`deflines mpyuw_task_m;
begin
  av2_inst = 1'b1;
   mpy_op     = 1'b1;
   half_size  = 1'b1;
   z_write    = 1'b1;
   n_write    = 1'b1;
   v_write    = 1'b1;
end
`enddeflines

`deflines mpylo_task_m;
begin
  av2_inst = 1'b1;
   mpy_op     = 1'b1;
   signed_op  = 1'b1;
   z_write    = 1'b1;
   n_write    = 1'b1;
   v_write    = 1'b1;
end
`enddeflines


`deflines mpyhi_task_m;
begin
  av2_inst = 1'b1;
   mpy_op     = 1'b1;
   byte_size  = 1'b1;       // selects upper 32-bits of result
   signed_op  = 1'b1;
   z_write    = 1'b1;
   n_write    = 1'b1;
   v_write    = 1'b1;
end
`enddeflines


`deflines mpylou_task_m;
begin
  av2_inst = 1'b1;
   mpy_op     = 1'b1;
   z_write    = 1'b1;
   n_write    = 1'b1;
   v_write    = 1'b1;
end
`enddeflines


`deflines mpyhiu_task_m;
begin
  av2_inst = 1'b1;
   mpy_op     = 1'b1;
   byte_size  = 1'b1;       // selects upper 32-bits of result
   z_write    = 1'b1;
   n_write    = 1'b1;
   v_write    = 1'b1;
end
`enddeflines


`deflines div_task_m;
begin
  av2_inst = 1'b1;
  div_op     = 1'b1;
  signed_op  = 1'b1;
  z_write    = 1'b1;  // set if quotient is zero
  n_write    = 1'b1;  // set if quotient is negative
  v_write    = 1'b1;  // set if operand 2 is zero
end
`enddeflines

`deflines divu_task_m;
begin
  av2_inst = 1'b1;
  div_op     = 1'b1;
  z_write    = 1'b1;  // set if quotient is zero
  n_write    = 1'b1;  // always cleared
  v_write    = 1'b1;  // set if operand 2 is zero
end
`enddeflines

`deflines rem_task_m;
begin
  av2_inst = 1'b1;
  div_op     = 1'b1;
  byte_size  = 1'b1;  // encodes rem operator within divide unit
  signed_op  = 1'b1;
  z_write    = 1'b1;  // set if remainder is zero
  n_write    = 1'b1;  // set if remainder is negative
  v_write    = 1'b1;  // set if operand 2 is zero
end
`enddeflines

`deflines remu_task_m;
begin
  av2_inst = 1'b1;
  div_op     = 1'b1;
  byte_size  = 1'b1;  // encodes rem operator within divide unit
  z_write    = 1'b1;  // set if remainder is zero
  n_write    = 1'b1;  // always cleared
  v_write    = 1'b1;  // set if operand 2 is zero
end
`enddeflines

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Memory load / store instruction decode tasks                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines ld_s_rr_task_m;
begin
  av2_inst = 1'b1;
  load = 1'b1;
end
`enddeflines

`deflines ldb_s_rr_task_m;
begin
  av2_inst = 1'b1;
  load = 1'b1;
  byte_size = 1'b1;
end
`enddeflines

`deflines ldw_s_rr_task_m;
begin
  av2_inst = 1'b1;
  load = 1'b1;
  half_size = 1'b1;
end
`enddeflines

`deflines load_16_task_m;
begin
  av2_inst = 1'b1;
  load = 1'b1;
  `npuarc_regs_c_dest_16_task_m;
  `npuarc_regs_b_src1_16_task_m;
  shimm = { 27'd0, inst[20:16] };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines store_16_task_m;
begin
  av2_inst = 1'b1;
  store = 1'b1;
  opd3_sel = 1'b1;
  `npuarc_regs_b_src1_16_task_m;
  `npuarc_regs_c_src2_16_task_m;
  shimm = { 27'd0, inst[20:16] };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines load_rr_32_task_m;
begin
  av2_inst  = 1'b1;
  load      = 1'b1;
  signed_op = inst[16];
  cache_byp = inst[15];
  `npuarc_regs_a1bc_32_task_m;
  `npuarc_add_16_task_m;
  pref      = (rf_wenb1 == 1'b0); 

  case ( inst[18:17] )
  2'd0: illegal_instr = signed_op & (!pref);  // illegal if not PREALLOC
  2'd1: byte_size     = 1'b1;
  2'd2: half_size     = 1'b1;
  2'd3: 
  begin
    double_size       = 1'b1;
    illegal_instr     = signed_op & (!pref); // illegal if not PREALLOC
  end
  default:;
  endcase

  rf_wenb1_64 = rf_wenb1 & double_size;

  
  case ( inst[23:22] )
   2'd0: ; // No modifier

   2'd1, // .A or .AW mode
   2'd2: // .AB mode
    begin
    rf_wenb0      = ~(  limm_r0 
                      | (rf_ra0 == 6'd61) 
                      | (rf_ra0 == 6'd63));
    rf_wa0        = rf_ra0;
    pre_addr      = (inst[22] == 0);
    illegal_instr = illegal_instr      // update to r62,r60,r63 is illegal
                  | limm_r0 
                  | (rf_ra0 == 6'd61) 
                  | (rf_ra0 == 6'd63);
    end

   2'd3: // .AS mode
    case ( inst[18:17] )
     2'd0:   src2_sh2      = 1'b1;
     2'd1:   illegal_instr = 1'b1;
     2'd2:   src2_sh1      = 1'b1;
     2'd3:   src2_sh2      = 1'b1;
    default: ;
    endcase
  endcase
  illegal_instr = illegal_instr | (pref & signed_op & cache_byp);
end
`enddeflines

`deflines load_32_task_m;
begin
  av2_inst  = 1'b1;
  load      = 1'b1;
  shimm     = { {24{inst[15]}}, inst[23:16] };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;

  signed_op = inst[6];
  cache_byp = inst[11];
  pref      = (rf_wenb1 == 1'b0);
  case ( inst[8:7] )
  2'd0: illegal_instr = signed_op & (!pref);  // illegal if not PREALLOC
  2'd1: byte_size     = 1'b1;
  2'd2: half_size     = 1'b1;
  2'd3: 
  begin
    double_size       = 1'b1;
    illegal_instr     = signed_op & (!pref); // illegal if not PREALLOC
  end
  default:;
  endcase

  rf_wenb1_64 = rf_wenb1 & double_size;

  case ( inst[10:9] )
   2'd0: ; // No modifier

   2'd1, // .A or .AW mode
   2'd2: // .AB mode
    begin
    rf_wenb0      = ~(  limm_r0 
                      | (rf_ra0 == 6'd61) 
                      | (rf_ra0 == 6'd63));
    rf_wa0        = rf_ra0;
    pre_addr      = (inst[9] == 0);
    illegal_instr = illegal_instr      // update to r62,r60,r63 is illegal
                  | limm_r0 
                  | (rf_ra0 == 6'd61) 
                  | (rf_ra0 == 6'd63);
    end

   2'd3: // .AS mode
    case ( inst[8:7] )
     2'd0:   src2_sh2      = 1'b1;
     2'd1:   illegal_instr = 1'b1;
     2'd2:   src2_sh1      = 1'b1;
     2'd3:   src2_sh2      = 1'b1;
    default: ;
    endcase
  endcase
  illegal_instr = illegal_instr | (pref & signed_op & cache_byp);
end
`enddeflines

`deflines store_32_task_m;
begin
  av2_inst = 1'b1;
  store = 1'b1;
  opd3_sel = 1'b1;
  shimm = { {24{inst[15]}}, inst[23:16] };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;

  case ( inst[2:1] )
  2'd1: byte_size     = 1'b1;
  2'd2: half_size     = 1'b1;
  2'd3: double_size   = 1'b1;
  default:;
  endcase

  case ( inst[4:3] )
   2'd0: ; // No modifier

   2'd1, // .A or .AW mode
   2'd2: // .AB mode
    begin
    rf_wenb0      = ~(  limm_r0 
                      | (rf_ra0 == 6'd61) 
                      | (rf_ra0 == 6'd63));
    rf_wa0        = rf_ra0;
    pre_addr      = (inst[3] == 0);
    illegal_instr = illegal_instr      // update to r62,r60,r63 is illegal
                  | limm_r0 
                  | (rf_ra0 == 6'd61) 
                  | (rf_ra0 == 6'd63);
    end

   2'd3: // .AS mode
    case ( inst[2:1] )
     2'd0:   src2_sh2      = 1'b1;
     2'd1:   illegal_instr = 1'b1;  //.AS mode is illegal for LDB
     2'd2:   src2_sh1      = 1'b1;
     2'd3:   src2_sh2      = 1'b1;
    default: ;
    endcase
  endcase

  cache_byp = inst[5];

  // Additional decoding to support store-immediate for
  // ARCompact v2 ISA.
  stimm_op =  inst[0];                 // select immediate data to store
  rf_renb1 = (~inst[0]) & (~limm_r1);  // disable read of 'c' register
end
`enddeflines

`deflines ex_task_m;
begin
  av2_inst = 1'b1;
  store     = 1'b1;     // EX instruction performs both
  load      = 1'b1;     // a Load and a Store operation.
  pre_addr  = 1'b1;     // use src2 without adding to src1
  mov_op    = inst[22];
  cache_byp = inst[15]; // Get the .DI bit

  // Re-direct the EX load result to port 1, as this value is
  // returning from memory.
  //
  rf_wenb0  = 1'b0;     // No update via port 0
  rf_wenb1  = 1'b1;     // Write 'b' register via port 1
  rf_wa1    = rf_ra1;   // Destination register is 'b', on rf_ra1
end
`enddeflines

`deflines llock_task_m;
begin
  av2_inst    = 1'b1;
  load        = 1'b1;
  locked      = 1'b1;
//  pre_addr    = 1'b1;     // use src2 without adding to src1
  mov_op      = inst[22]; // select AGU src2 if opd is u6
  cache_byp   = inst[15]; // get the .DI bit
  double_size = inst[1];  // 64-bit LLOCKD if inst[1] is set

  // Re-direct the llock result to port 1, as this value is
  // returning from memory.
  //
  rf_wenb0    = 1'b0;     // No update via port 0
  rf_wa1      = { inst[14:12], inst[26:24] };
  rf_wenb1    = ({inst[14:12], inst[26:24]} != 6'd62);
  rf_wenb1_64 = rf_wenb1 & double_size;
end
`enddeflines

`deflines scond_task_m;
begin
  av2_inst    = 1'b1;
  store       = 1'b1;
  locked      = 1'b1;
  pre_addr    = 1'b1;     // use src2 without adding to src1
  mov_op      = inst[22]; // select AGU src2 if opd is u6
  cache_byp   = inst[15]; // get the .DI bit
  double_size = inst[1];  // 64-bit SCONDD if inst[1] is set  
  z_write     = 1'b1;     // enable SCOND to update Z flag
  flag_enable = 1'b1;     // SCOND always updates flags
  rf_wenb0    = 1'b0;     // No update via port 0
end
`enddeflines

`deflines mem_sp_16_task_m;
begin
  av2_inst = 1'b1;
  shimm = { 27'd0, inst[20:16] };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines r0_gp_16_task_m;
begin
  av2_inst = 1'b1;
  rf_wa1 = 6'd0;
  rf_wenb1 = 1'b1;
  shimm = { {24{inst[24]}}, inst[23:16] };
  sel_shimm = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines load_pcl_16_task_m;
begin
  av2_inst = 1'b1;
  load = 1'b1;
  `npuarc_regs_b_ld_dest_16_task_m;
  shimm = { 24'd0, inst[23:16] };
  sel_shimm = 1'b1;
  src2_sh2 = 1'b1;
  `npuarc_add_16_task_m;
end
`enddeflines

`deflines mv_imm_16_task_m;
begin
  av2_inst = 1'b1;
  `npuarc_regs_b_dest_16_task_m;
  shimm = { 24'd0, inst[23:16] };
  sel_shimm = 1'b1;
  mov_op = 1'b1;          // MOV src2 to dst
  fast_op = 1'b1;
end
`enddeflines

`deflines arith_sp_sp_task_m;
begin
  av2_inst = 1'b1;
  rf_wa0 = 6'd28;
  rf_wenb0 = 1'b1;
  shimm = { 27'd0, inst[20:16] };
  sel_shimm = 1'b1;
  src2_sh2 = 1'b1;
end
`enddeflines

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Load and Store Aux Regs, and related tasks                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines lr_task_m;
begin
  av2_inst      = 1'b1;
  lr_op         = 1'b1;
  opds_in_sa    = 1'b1;
end
`enddeflines

`deflines sr_task_m;
begin
  av2_inst       = 1'b1;
  sr_op          = 1'b1;
  opds_in_sa     = 1'b1;
  opd3_sel       = 1'b1;
end
`enddeflines

`deflines seti_task_m;
begin
  av2_inst   = 1'b1;
  `npuarc_zero_operand_task_m;

  flag_op    = 1'b1;
  cache_byp  = 1'b1;
  kernel_op  = 1'b1;

  // Identify as SETI/CLRI
  signed_op  = 1'b1;

  shimm      = { 26'd0, inst[11:6] };
  sel_shimm  = inst[22];

  if (inst[15] == 1'b1)
    `npuarc_inst_err_task_m;
  opds_in_sa = 1'b1;
end
`enddeflines

`deflines clri_task_m;
begin
  av2_inst  = 1'b1;
  flag_op   = 1'b1;
  cache_byp = 1'b0;
  kernel_op = 1'b1;
  rf_wa0    = inst[11:6];
  rf_wenb0  = (inst[23:22] == 2'b00) & (rf_wa0 != 6'd62);
  // Identify as SETI/CLRI
  signed_op = 1'b1;

  if (inst[15] == 1'b1)
    `npuarc_inst_err_task_m;
  opds_in_sa = 1'b1;
end
`enddeflines

`deflines aex_task_m;
begin
  av2_inst  = 1'b1;
  sr_op     = 1'b1;     // AEX instruction performs both
  lr_op     = 1'b1;     // an LR and an SR operation.

  opd3_sel  = 1'b1;
  illegal_operand = (rf_ra0 == 6'd62) | (rf_ra0 == 6'd63);

  opds_in_sa = 1'b1;      // must have operands in SA stage

  // Re-direct the AEX result to the b-reg source register, 
  // as this value is returning from memory.
  //
  rf_wa0    = rf_ra0;   // Destination register is 'b' register
end
`enddeflines

`deflines flag_task_m;
begin                     // or halt processor if H-bit set
  av2_inst        = 1'b1;
  flag_op         = 1'b1;
  cache_byp       = inst[15];   // indicates a kflag operation
  opds_in_sa      = 1'b1;
end
`enddeflines


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Jump micro-code tasks                                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines jcc_task_m;
begin
  av2_inst = 1'b1;
  jump     = 1'b1;        // select jump functionality
  dslot    = inst[16];
  if ((dslot == 1'b1) && (limm_r1 == 1'b1))
  begin
    `npuarc_inst_err_task_m;
  end
  opd3_sel = 1'b1;        // target is always via src2 operand
end
`enddeflines


`deflines j_s_task_m;
begin
  av2_inst = 1'b1;
  jump     = 1'b1;        // select jump functionality
  dslot    = inst[21];
  opd3_sel = 1'b0;        // target is always via src1 operand
end
`enddeflines


`deflines jeq_s_task_m;
begin
  av2_inst = 1'b1;
  jump     = 1'b1;        // select jump functionality
  opd3_sel = 1'b1;        // target is always via src2 operand

  // q_field[4] is always 0 for non-extension instructions
  //
  q_field[3:0] = 4'b0001; // EQ condition
end
`enddeflines


`deflines jne_s_task_m;
begin
  av2_inst = 1'b1;
  jump     = 1'b1;        // select jump functionality
  opd3_sel = 1'b1;        // target is always via src2 operand

  // q_field[4] is always 0 for non-extension instructions
  //
  q_field[3:0] = 4'b0010; // NE condition
end
`enddeflines


`deflines j_blink_task_m;
begin
  av2_inst = 1'b1;
  jump     = 1'b1;        // select jump functionality
  opd3_sel = 1'b1;        // target is always via src2 operand
  dslot    = inst[24];
end
`enddeflines


`deflines jlcc_task_m;
begin
  av2_inst = 1'b1;
  mov_op   = 1'b1;        // to move link address from src2 to primary result
  jump     = 1'b1;        // select jump functionality
  link     = 1'b1;
  rf_wa0   = 6'd31;       // BLINK register
  rf_wenb0 = 1'b1;        // which gets written if jump is taken
  dslot    = inst[16];
  if ((dslot == 1'b1) && (limm_r1 == 1'b1))
  begin
    `npuarc_inst_err_task_m;
  end
  opd3_sel = 1'b1;        // target is always via src2 operand
  fast_op  = 1'b1;        // link value available immediately
end
`enddeflines


`deflines jl_s_task_m;
begin
  av2_inst = 1'b1;
  mov_op   = 1'b1;        // to move link address from src2 to primary result
  jump     = 1'b1;        // select jump functionality
  link     = 1'b1;
  rf_wa0   = 6'd31;       // BLINK register
  rf_wenb0 = 1'b1;        // which gets written if jump is taken
  dslot    = inst[21];
  opd3_sel = 1'b0;        // target is always via src1 operand
  fast_op  = 1'b1;        // link value available immediately
end
`enddeflines


`deflines lpcc_task_m;
begin
  av2_inst = 1'b1;
  loop_op    = 1'b1;      // tell datapath we're doing an LPcc
  rel_branch = 1'b1;      // lp_end needs relative offset + PC
  opds_in_sa = 1'b1;
end                       // format decode gets the rest...
`enddeflines


`deflines trap_s_task_m;
begin
  av2_inst       = 1'b1;
  flag_enable    = 1'b0;  // trap_s does not affect the ZNCV flags
  trap_op        = 1'b1;

  shimm          = {26'd0, inst[26:21]};
  sel_shimm      = 1'b1;

  byte_size      = 1'b1;  // differentiates trap_s from trap0/swi
  opds_in_sa     = 1'b1;
end
`enddeflines

`deflines nop_s_task_m;
begin
  av2_inst    = 1'b1;
end
`enddeflines

`deflines swi_task_m;
begin
  av2_inst = 1'b1;
  flag_enable = 1'b0;  // swi does not affect the ZNCV flags
  trap_op     = 1'b1;  // uses trap_op ucode, with byte_size == 0
  `npuarc_zero_operand_task_m;

  // SWI requires bit 15 to be 0
  if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
    `npuarc_inst_err_task_m;
  opds_in_sa = 1'b1;
end
`enddeflines

`deflines swi_s_task_m;
begin
  av2_inst    = 1'b1;
  flag_enable = 1'b0;  // swi does not affect the ZNCV flags
  trap_op     = 1'b1;  // uses trap_op ucode, with byte_size == 0
  `npuarc_zero_operand_task_m;
  opds_in_sa = 1'b1; 
  sel_shimm  = 1'b1;   // ECR.param <= 0
end
`enddeflines

`deflines sleep_task_m;
begin
  av2_inst  = 1'b1;
  
  // set sleep_op unless this is a WLFC insn and STATUS32.US == 0
  // and the processor is in User mode.
  //
  sleep_op  = (!aux_stat32_u_r) | aux_stat32_us_r | (!inst[24]);
  
  // set kernel_op for SLEEP, or for WEVT when STATUS32.US == 0
  //
  kernel_op = (!inst[12]) | ((!aux_stat32_us_r) & (!inst[24]));

  // overload half_size and byte_size to indicate WEVT and WLFC
  //
  half_size = inst[12];   // half_size indicates either WEVT or WLFC
  byte_size = inst[24];   // byte_size differentiates WLFC (1) from WEVT (0)

  shimm     = { 26'd0, inst[11:6] };
  sel_shimm = inst[22];


  if (inst[15] == 1'b1)   // SLEEP requires bit 15 to be 0
    `npuarc_inst_err_task_m;
  opds_in_sa = 1'b1;
end
`enddeflines

`deflines brk_task_m;
begin
  av2_inst = 1'b1;
  kernel_op = !aux_dbg_ub_r;  // Kernel op when DEBUG.UB == 0
  `npuarc_zero_operand_task_m;
  // BRK requires bit 15 to be 0
  if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
    `npuarc_inst_err_task_m;
  else
    brk_op    = 1'b1;

  opds_in_sa = 1'b1;
end
`enddeflines

`deflines brk_s_task_m;
begin
  av2_inst = 1'b1;
  
  if (inst[26:21] == 6'b111111)
    begin                       // brk_s
    brk_op    = 1'b1;
    kernel_op = !aux_dbg_ub_r;  // Kernel op when DEBUG.UB == 0
    end
  else
    begin                       // swi_s u6
    trap_op    = 1'b1;          // swi_s uses trap_op ucode, with byte_size == 0
    shimm      = {26'd0, inst[26:21]};
    sel_shimm  = 1'b1;          // ECR.param <= inst[26:21]
    opds_in_sa = 1'b1;
    end
  `npuarc_zero_operand_task_m;
end
`enddeflines

`deflines sync_task_m;
begin
  av2_inst  = 1'b1;
  sync_op   = ~inst[12]; // excludes DSYNC and DMB
  dsync_op  = inst[12] & (~inst[24]);
  dmb_op    = inst[12] &  inst[24];
  dmb_type  = inst[8:6];
  `npuarc_zero_operand_task_m;

  if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
    `npuarc_inst_err_task_m;
  
end
`enddeflines

`deflines rtie_task_m;
begin
  av2_inst  = 1'b1;
  kernel_op = 1'b1;       // Kernel-only instruction
  opd3_sel  = 1'b0;
  sel_shimm = 1'b0;
  multi_op  = 1'b1;
  `npuarc_zero_operand_task_m;

  if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
    `npuarc_inst_err_task_m;
  else
    rtie_op   = 1'b1;

  opds_in_sa = 1'b1;
end
`enddeflines

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Branch micro-code tasks                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`deflines br_cond_task_m;
begin
  av2_inst = 1'b1;
  bcc           = 1'b1;
  rel_branch    = 1'b1;
  dslot         = inst[5];
  offset        = { {11{inst[15]}}, inst[15:6], inst[26:17], 1'b0 };
  `npuarc_regs_q_32_task_m;
end
`enddeflines


`deflines bcc_s_task_m;
begin
  av2_inst = 1'b1;
  is_16bit   = 1'b1;
  bcc        = 1'b1;
  rel_branch = 1'b1;

  // q_field[4] is always 0 for non-extension instructions

  if (inst[26:25] != 2'b11)
    begin
    // inst[26:25]  operation  q_field[3:0]
    // ------------------------------------
    //    00:        b_s          0000
    //    01:        beq_s        0001
    //    10:        bne_s        0010
    // ------------------------------------
    //
    offset       = { {22{inst[24]}}, inst[24:16], 1'b0 };
    q_field[3:0] = {2'b00, inst[26:25]};
    end
  else
    begin
      // inst[24:22]  operation  q_field[3:0]
      // ------------------------------------
      //   000:        bgt_s         1001
      //   001:        bge_s         1010
      //   010:        blt_s         1011
      //   011:        ble_s         1100
      //   100:        bhi_s         1101
      //   101:        bhs_s         0110
      //   110:        blo_s         0101
      //   111:        bls_s         1110
      // ------------------------------------
      //
      offset  = { {25{inst[21]}}, inst[21:16], 1'b0 };

      case ( inst[24:22] )
      3'b000: q_field[3:0] = 4'b1001; // bgt_s
      3'b001: q_field[3:0] = 4'b1010; // bge_s
      3'b010: q_field[3:0] = 4'b1011; // blt_s
      3'b011: q_field[3:0] = 4'b1100; // ble_s
      3'b100: q_field[3:0] = 4'b1101; // bhi_s
      3'b101: q_field[3:0] = 4'b0110; // bhs_s
      3'b110: q_field[3:0] = 4'b0101; // blo_s
      3'b111: q_field[3:0] = 4'b1110; // bls_s
      endcase
    end
end

`enddeflines


`deflines br_ucond_task_m;
begin
  av2_inst = 1'b1;
  bcc           = 1'b1;
  rel_branch    = 1'b1;

  // q_field[4] is always 0 for non-extension instructions
  //
  q_field[3:0]  = 4'b0000;  // branch always

  dslot         = inst[5];
  offset        = { {7{inst[3]}}, inst[3:0], inst[15:6], inst[26:17], 1'b0 };
end
`enddeflines

`deflines grp_b_target_task_m;
begin
  bcc        = 1'b1;      // behaves like a bcc instruction
  rel_branch = 1'b1;      // select relative branch
  offset     = { 20'd0, inst[25:16], 2'b00 };
end
`enddeflines

`deflines jli_s_task_m;
begin
  av2_inst = 1'b1;
  `npuarc_grp_b_target_task_m;
  jli_src0   = 1'b1;      // select JLI_BASE aux register as src0
  link       = 1'b1;
  fast_op    = 1'b1;      // link value is available in 1 cycle
  rf_wa0     = 6'd31;     // BLINK register
  rf_wenb0   = 1'b1;      // gets written by this instruction
end
`enddeflines

`deflines bi_task_m;
begin
  av2_inst = 1'b1;
  if (inst[15] == 1'b1)   // the <.f> bit must be zero
    `npuarc_inst_err_task_m;

  src2_sh2   = ~inst[16]; // BI  operation shifts [c] 2 places
  src2_sh1   =  inst[16]; // BIH operation shifts [c] 1 place
  add_op     = 1'b1;         // add PC and (c << 1 or 2)
  btab_op    = 1'b1;         // ucode for BI and BIH
  opds_in_sa = 1'b1;      // must have operands in SA stage
end
`enddeflines

`deflines bl_cond_task_m;
begin
  av2_inst = 1'b1;
  bcc        = 1'b1;
  rel_branch = 1'b1;
  `npuarc_regs_q_32_task_m;        // branch according CC
  link       = 1'b1;
  mov_op     = 1'b1;      // to move link address from src2 to primary result
  fast_op    = 1'b1;      // link value gets computed in 1 cycle
  rf_wa0     = 6'd31;     // BLINK register
  rf_wenb0   = 1'b1;      // which gets written if branch taken
  dslot      = inst[5];
  offset     = { {11{inst[15]}}, inst[15:6], inst[26:18], 2'b00 };
end
`enddeflines


`deflines bl_s_ucond_task_m;
begin
  av2_inst = 1'b1;
  bcc        = 1'b1;
  rel_branch = 1'b1;

  // q_field[4] is always 0 for non-extension instructions
  //
  q_field[3:0] = 4'b0000;  // branch always

  link       = 1'b1;
  mov_op   = 1'b1;        // to move link address from src2 to primary result
  fast_op    = 1'b1;      // link value gets computed in 1 cycle
  fast_op    = 1'b1;      // link value available immediately
  rf_wa0     = 6'd31;     // BLINK register
  rf_wenb0   = 1'b1;      // which gets written unconditionally
  offset     = { {20{inst[26]}}, inst[25:16], 2'b00 };
end
`enddeflines


`deflines bl_ucond_task_m;
begin
  av2_inst = 1'b1;
  bcc        = 1'b1;
  rel_branch = 1'b1;

  // q_field[4] is always 0 for non-extension instructions
  //
  q_field[3:0] = 4'b0000;  // branch always

  link       = 1'b1;
  mov_op   = 1'b1;        // to move link address from src2 to primary result
  fast_op    = 1'b1;      // link value available immediately
  rf_wa0     = 6'd31;     // BLINK register
  rf_wenb0   = 1'b1;      // which gets written unconditionally
  dslot      = inst[5];
  offset     = { {7{inst[3]}}, inst[3:0], inst[15:6], inst[26:18], 2'b00 };
end
`enddeflines


`deflines brcc_bbit_task_m;
begin
  // Branch tests that can be performed for BRcc or BBITn:
  // In Albacore the BRcc comparisons are performed by a comparator
  // that is separate from the Adder, within the X1 and CA ALUs.
  // This is a speed optimization.
  
  //  Inst   Test performed cc_field Unit Logic
  //  --------------------------------------------
  //  BREQ   Zero             000     A    Z
  //  BRNE   Non-zero         001     A   ~Z
  //  BRLT   Less-than        010     A    N != V
  //  BRGE   Greater-or-equal 011     A   ~(N != V)
  //  BRLO   Unsigned Lower   100     A    C
  //  BRHS   Unsigned greater 101     A   ~C
  //  --------------------------------------------
  //  BBIT0  Zero             000     L    Z
  //  BBIT1  Non-zero         001     L   ~Z
  //  --------------------------------------------
  //
  //  The cc_field is used to encode the comparisons used by
  //  a BRcc, BBITn or SETcc instruction. This is a separate
  //  field from the q_field, which is used to encode instruction
  //  predicates or status-based branch decisions.

  av2_inst = 1'b1;

  // Extract the register and/or u6 source operands, as required
  //
  case ( inst[4] )
  1'b0: `npuarc_regs_bc_32_task_m;
  1'b1: `npuarc_regs_bu6_32_task_m;
  endcase

  // Signal whether there is a delay slot instruction following
  //
  dslot         = inst[5];

  // Instruction is illegal if there's a delay slot and limm
  //
  illegal_instr = inst[5] & (limm_r0 | limm_r1);


  // Set ucode bit to signal BRcc or BBITn branch operations
  //
  brcc_bbit     = 1'b1;

  // Assign ALU operation control bits
  //
  and_op        =  bit_op;              // use logical AND for BBITn ops
  bit_op        =  inst[2] & inst[1];   // BBIT0 and BBIT1 are bit ops
  src2_mask_sel =  bit_op;              // select mask operand for bit ops

  // select PC+offset as target
  //
  rel_branch    = 1'b1;

  // Extract branch offset from instruction word
  //
  offset        = { {24{inst[15]}}, inst[23:17], 1'b0 };

  // BRcc and BBITn can evaluate their boolean result in X1
  //
  fast_op       = 1'b1;

  // Assign condition-selection control bits
  //
  case ( inst[2:0] )
  3'h0:  cc_field = 3'h0;
  3'h1:  cc_field = 3'h1;
  3'h2:  cc_field = 3'h2;
  3'h3:  cc_field = 3'h3;
  3'h4:  cc_field = 3'h4;
  3'h5:  cc_field = 3'h5;
  3'h6: cc_field = 3'h0;
  3'h7: cc_field = 3'h1;
  endcase

end
`enddeflines


`deflines setcc_task_m;
begin
  // SETcc conditions are identical to those for BRcc
  //
  //  Inst    Test performed  cc_bits Subtract flag test
  //  ---------------------------------------------------
  //  SETEQ  src1 ==  src2     000     Z
  //  SETNE  src1 !=  src2     001    ~Z
  //  SETLT  src1 <s  src2     010     N != V
  //  SETGE  src1 >=s src2     011    ~(N != V)
  //  SETLO  src1 <u  src2     100     C
  //  SETHS  src1 >=u src2     101    ~C
  //  SETLE  src1 >s  src2     110    ~(N != V) & ~Z
  //  SETGT  src1 <=s src2     111    (N != V) | Z
  //  ---------------------------------------------------
  //
  av2_inst  = 1'b1;
  setcc_op  = 1'b1;         // set the ucode bit for SETcc
  add_op    = 1'b1;         // perform subtraction to get flag results
  force_cin = 1'b1;         // compute A + ~B + 1
  inv_src2  = 1'b1;         // select ~B as src2
  fast_op   = 1'b1;         // allow next-cycle forwarding of result
  z_write   = 1'b1;         // also update Z flag if F-bit is set
  n_write   = 1'b1;         // also update N flag if F-bit is set
  c_write   = 1'b1;         // also update C flag if F-bit is set
  v_write   = 1'b1;         // also update V flag if F-bit is set
  cc_field  = inst[18:16];  // assign condition-selection control bits
end
`enddeflines


`deflines brcc_s_task_m;
begin
  av2_inst  = 1'b1;

  // Set ucode bit to signal late-evaluated BRcc/BBITn
  //
  brcc_bbit = 1'b1;

  // select PC+offset as target
  //
  rel_branch = 1'b1;

  // Assign condition-selection control bits
  // These bits are used to select a conditional
  // result from the comparison performed in this
  // instruction. Bit 23 of the instruction indicates
  // whether breq_s (0) or brne_s (1) is selected.
  //
  cc_field   = {2'b0, inst[23]};

  // Extract branch offset from instruction word
  //
  offset  = { {24{inst[22]}}, inst[22:16], 1'b0 };
end
`enddeflines
