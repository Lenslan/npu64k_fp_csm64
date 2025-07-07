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
// #####                                #
//  #   #                               #
//  #   #                               #
//  #   #   ####    ####    ####    ### #   ####
//  #   #  #    #  #    #  #    #  #   ##  #    #
//  #   #  ######  #       #    #  #    #  ######
//  #   #  #       #       #    #  #    #  #
//  #   #  #    #  #    #  #    #  #   ##  #    #
// #####    ####    ####    ####    ### #   ####
//
// ===========================================================================
//
// Description:
//
//  This file implements a set of instruction decode tasks for the
//  ARCv2 instruction set.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Definitions for all decode-related constants
//
`include "npuarc_decode_const.v"

// Definitions for the micro-code constants, including both ARC base-case
// and User extension instructions.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_decode (
  input   [`npuarc_DATA_RANGE]       inst,             // instruction to be decoded
  input                       pre_limm_r0,      // has a LIMM rather than reg 0
  input                       pre_limm_r1,      // has a LIMM rather than reg 1
  input                       pre_rf_renb0,     // read enable for reg port 0
 input                        pre_rf_renb0_64,  // port 0 64-bit read enable
  input                       pre_rf_renb1,     // read enable for reg port 1
  input                       pre_rf_renb1_64,  // port 1 64-bit read enable
  input  [`npuarc_RGF_ADDR_RANGE]    pre_rf_ra0,       // read address for reg port 0
  input  [`npuarc_RGF_ADDR_RANGE]    pre_rf_ra1,       // read address for reg port 1
  input                       aux_dbg_ub_r,     // DEBUG.UB flag
  input                       aux_stat32_us_r,  // STATUS32.US flag
  input                       aux_stat32_u_r,   // STATUS32.U flag
  input                       eia_inst_valid,   // 1=> EIA inst was decoded
  input                       eia_decode_src64, // eia inst has 64-bit source opds
  input                       eia_multi_cycle,  // 1=> EIA inst is multi-cycle
  input                       eia_ra0_is_ext,   // rf_ra0 is EIA core register
  input                       eia_ra1_is_ext,   // rf_ra1 is EIA core register
  input                       eia_wa0_is_ext,   // rf_wa0 is EIA core register
  input                       eia_wa1_is_ext,   // rf_wa0 is EIA core register
  input                       eia_illegal_cond, // q_field is illegal condition
  input                       eia_kernel,       // kernel priv needed
  input                       eia_illegal_cr_access,  // ro/wo violations

  input                       uop_valid_r,      // insn. is a uop.

  output [`npuarc_DA_CODE_WIDTH-1:0] acode             // decoded micro-code output
);

//////////////////////////////////////////////////////////////////////////////
// Micro-code field declarations                                            //
//////////////////////////////////////////////////////////////////////////////

// Declare the ARC micro-code fields for base-case instructions
//
// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

reg  [5:0] rf_wa0;  // Register address for write port 0
reg rf_wenb0;  // Register write enable for write port 0
reg rf_wenb0_64;  // 64-bit write enable for write port 0
reg cc_byp_64_haz;  // Unable to bypass 64-bit result to SA
reg has_limm;  // Instruction has LIMM data
reg is_16bit;  // Instruction is 16-bit encoded
reg sr_op;  // Decodes an |SR| instruction
reg loop_op;  // Decodes an |LPcc| instruction
reg locked;  // Set if mem-op is locked
reg wa0_lpc;  // Set if write port 0 selects |LP_COUNT| register
reg dslot;  // Set if control transfer has a delay slot instruction
reg sleep_op;  // Decodes the |SLEEP| instruction
reg acc_wenb;  // Set if implicit write to the accumulator
reg writes_acc;  // ACCL or ACCH is an explicit register destination
reg lr_op;  // Decodes an |LR| instruction
reg jump;  // Decodes jump instructions |Jcc| and |JLcc|
reg load;  // Decodes all forms of |load| instruction
reg pref;  // Set if |load| is a pref instruction
reg store;  // Decodes all forms of |store| instruction
reg uop_prol;  // Instruction is terminal of PROL sequence
reg  [5:0] rf_wa1;  // Register address for write port 1
reg rf_wenb1;  // Register write enable for write port 1
reg rf_wenb1_64;  // 64-bit write enable for write port 1
reg signed_op;  // Set if operation is signed
reg double_size;  // Set if operation is 64-bit
reg half_size;  // Set if operation is 16-bit
reg byte_size;  // Set if operation is 8-bit
reg rtie_op;  // Decodes the |RTIE| instruction
reg enter_op;  // Decodes the |ENTER_S| instruction
reg leave_op;  // Decodes the |LEAVE_S| instruction
reg trap_op;  // Decodes the |TRAP0| or |TRAP_S| instruction
reg sync_op;  // Decodes the |SYNC| instruction
reg brk_op;  // Decodes the |BRK| or |BRK_S| instruction
reg invalid_instr;  // Set if instruction is not recognised
reg rgf_link;  // Set if ILINK regs are accessed
reg prod_sign;  // sign of 32x32 mac product
reg macu;  // indicates MACU, MACDU, MPYU or MPYDU operation
reg quad_op;  // Set if performing dual SIMD operation
reg acc_op;  // Set if accumulator is used by fixed-point operation
reg vector_op;  // Set if performing vector operation
reg dual_op;  // Set if performing dual SIMD operation
reg mpy_op;  // Set if performing multiply operation
reg z_wen;  // Write enable for |Z| bit in |STATUS32| register
reg n_wen;  // Write enable for |N| bit in |STATUS32| register
reg c_wen;  // Write enable for |C| bit in |STATUS32| register
reg v_wen;  // Write enable for |V| bit in |STATUS32| register
reg kernel_op;  // Set if instruction is privileged
reg flag_op;  // Decodes |FLAG| instruction
reg bcc;  // Decodes branch instructions |Bcc| and |BLcc|
reg link;  // Set if jump or branch enables linkage semantics (|JLcc|, |BLcc|)
reg brcc_bbit;  // Decodes compare-branch instructions |BRcc| and |BBITn|
reg cache_byp;  // Set if |load| or |store| bypasses the cache
reg slow_op;  // Indicates 2-cycle ALU op (must evaluate in X1 and X2)
reg fast_op;  // Indicates 1-cycle ALU op (can evaluate in X1 or CA)
reg div_op;  // Decodes |DIV|, |DIVU|, |REM| and |REMU|
reg btab_op;  // Perform a BI_S or BIH_S instruction
reg ei_op;  // Select EI_BASE as base addr in rel-branch, and do EI_S instruction
reg in_eslot;  // Instruction is in the exec-slot of a previous EI_S instruction
reg rel_branch;  // Set if control transfer uses a relative displacement
reg illegal_operand;  // Set if operand is illegal
reg swap_op;  // Decodes |SWAP| instruction
reg setcc_op;  // Decodes |SETcc| instructions
reg  [2:0] cc_field;  // Selects |BRcc|, |BBITn| or |SETcc| operator
reg  [4:0] q_field;  // Instruction predicate or branch condition
reg dest_cr_is_ext;  // Instruction has explicit extension core register destination
reg add_op;  // Set if Adder is enabled for this instruction
reg and_op;  // Set if logical AND operation is required for this instruction
reg or_op;  // Set if logical OR operation is required for this instruction
reg xor_op;  // Set if logical XOR operation is required for this instruction
reg mov_op;  // Set if operand 2 is moved to the destination
reg with_carry;  // Set if arithmetic or shift operation uses the |STATUS32.C| bit
reg simple_shift_op;  // Set if single-bit shift or rotate is required
reg left_shift;  // 1 $\rightarrow$ shift-left; 0 $\rightarrow$ shift-right
reg rotate_op;  // 1 $\rightarrow$ rotate; 0 $\rightarrow$ linear shift
reg inv_src1;  // Set if source operand 1 is to be inverted
reg inv_src2;  // Set if source operand 2 is to be inverted
reg bit_op;  // Selects a one-hot bit-mask in |maskgen| module
reg mask_op;  // Selects a bit-field mask in |maskgen| module for |BMSK| instruction
reg src2_mask_sel;  // Selects |maskgen|'s bit-mask as source operand 2
reg uop_commit;  // Instruction terminates uop. sequence
reg uop_epil;  // Instruction is terminal of EPIL sequence
reg uop_excpn;  // Instruction is terminal of Exception Epilogue
reg predicate;  // Instruction predicate, 0 => result updated is not allowed
reg rf_renb0;  // Register read enable for read port 0
reg rf_renb1;  // Register read enable for read port 1
reg rf_renb0_64;  // 64-bit read enable for read port 0
reg rf_renb1_64;  // 64-bit read enable for read port 1
reg  [5:0] rf_ra0;  // Register address for read port 0
reg  [5:0] rf_ra1;  // Register address for read port 1
reg jli_src0;  // Select JLI_BASE rather than PC as base addr in rel-branch
reg uop_inst;  // Instruction is part of a uop sequence
reg vec_shimm;  // vector of 16-bit SHIMM opds required
reg iprot_viol;  // speculative instruction fetch protection violation
reg dmb_op;  // Decodes the |DMB| instruction
reg  [2:0] dmb_type;  // Decodes the |DMB| sub-type
reg force_cin;  // Forces carry-in of 1 for Adder operation
reg opd3_sel;  // Select source 3: 1 $\rightarrow$ register 1; 0 $\rightarrow$ register 0
reg multi_op;  // Decodes a multi-operation insn.
reg abs_op;  // Decodes the |ABS| instruction
reg min_op;  // Decodes |MIN| instruction
reg max_op;  // Decodes |MAX| instruction
reg norm_op;  // Decodes |NORM| instruction
reg ldi_src0;  // Select LDI_BASE as base for register address calculation
reg pre_addr;  // Set if addressing mode uses pre-modified value
reg stimm_op;  // Indicates a store-immediate operation
reg src2_sh1;  // Enables 1-bit shift of source operand 2
reg src2_sh2;  // Enables 2-bit shift of source operand 2
reg src2_sh3;  // Enables 3-bit shift of source operand 2
reg barrel_shift_op;  // Set if multi-bit shift or rotate is required
reg opds_in_x1;  // Indicates op will require operands in X1 (starts in X2)
reg agu_uses_r0;  // AGU uses reg0 as a source operand
reg opds_in_sa;  // Indicates op will require operands in SA (starts in X1)
reg limm0_64;  // 64-bit LIMM required on read port 0
reg limm1_64;  // 64-bit LIMM required on read port 1
reg may_graduate;  // ACCL/ACCH could be explicit dest and insn may graduate
reg agu_uses_r1;  // AGU uses reg1 as a source operand
reg reads_acc;  // ACCL or ACCH is an explicit register operand
reg dsync_op;  // Decodes the |DSYNC| instruction
reg src2_shifts;  // Source operand 2 is shifted 1, 2 or 3 bits before the adder
reg sel_shimm;  // Selects a short-immediate operand (i.e. |S12|, |U6|, etc) as source operand 2
reg  [31:0] shimm;  // The short immediate operand, extended to 32-bits as required by the instruction
reg limm_r0;  // Set if register operand {\sf\bf b} is actually LIMM data
reg limm_r1;  // Set if register operand {\sf\bf c} is actually LIMM data
reg  [31:0] offset;  // Relative branch offset, sign-extended to 32-bits


//////////////////////////////////////////////////////////////////////////////
// Declare local register variables                                         //
//////////////////////////////////////////////////////////////////////////////

// The 'flag_enable' reg is derived by decoding the F-bit (bit 15) from
// instructions where the F-bit is defined. In all other cases the flag_enable
// reg will be turned off.
// The tasks for each instruction may set the z_write, n_write, c_write and
// v_write regs independently. These are then ANDed with flag_enable to create
// the z_wen, n_wen, c_wen and v_wen microcode bits for later use in the X1
// stage to control whether the Z, N, C and V flag bits are updated at the end
// of the instruction.

reg                         flag_enable;      // global flag enable
reg                         z_write;          // Z flag update enb
reg                         n_write;          // N flag update enb
reg                         c_write;          // C flag update enb
reg                         v_write;          // V flag update enb
reg                         av2_inst;         // instruction is ARCv2 defined
reg                         illegal_instr;    // instruction is illegal

//////////////////////////////////////////////////////////////////////////////
// Macro code task definitions                                              //
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Combinational instruction decode logic                                   //
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block W193 
// SMD: Empty statements
// SJ:  Simplify config code
// spyglass disable_block W71 
// SMD: Case statement does not have default
// SJ:  All cases covered
// leda W192 off
// LMD: Empty block statements
// LJ:  Simplify config code
// leda NTL_CON12 off
// LMD: Undriven net
// LJ:  Leda limitation (not undriven)
// leda B_3400 off
always @*
begin : decode_PROC

  // Initialise the local micro-code fields prior to decode
  //
// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

    rf_wa0 = 6'b0;  // generated code
    rf_wenb0 = 1'b0;  // generated code
    rf_wenb0_64 = 1'b0;  // generated code
    cc_byp_64_haz = 1'b0;  // generated code
    has_limm = 1'b0;  // generated code
    is_16bit = 1'b0;  // generated code
    sr_op = 1'b0;  // generated code
    loop_op = 1'b0;  // generated code
    locked = 1'b0;  // generated code
    wa0_lpc = 1'b0;  // generated code
    dslot = 1'b0;  // generated code
    sleep_op = 1'b0;  // generated code
    acc_wenb = 1'b0;  // generated code
    writes_acc = 1'b0;  // generated code
    lr_op = 1'b0;  // generated code
    jump = 1'b0;  // generated code
    load = 1'b0;  // generated code
    pref = 1'b0;  // generated code
    store = 1'b0;  // generated code
    uop_prol = 1'b0;  // generated code
    rf_wa1 = 6'b0;  // generated code
    rf_wenb1 = 1'b0;  // generated code
    rf_wenb1_64 = 1'b0;  // generated code
    signed_op = 1'b0;  // generated code
    double_size = 1'b0;  // generated code
    half_size = 1'b0;  // generated code
    byte_size = 1'b0;  // generated code
    rtie_op = 1'b0;  // generated code
    enter_op = 1'b0;  // generated code
    leave_op = 1'b0;  // generated code
    trap_op = 1'b0;  // generated code
    sync_op = 1'b0;  // generated code
    brk_op = 1'b0;  // generated code
    invalid_instr = 1'b0;  // generated code
    rgf_link = 1'b0;  // generated code
    prod_sign = 1'b0;  // generated code
    macu = 1'b0;  // generated code
    quad_op = 1'b0;  // generated code
    acc_op = 1'b0;  // generated code
    vector_op = 1'b0;  // generated code
    dual_op = 1'b0;  // generated code
    mpy_op = 1'b0;  // generated code
    z_wen = 1'b0;  // generated code
    n_wen = 1'b0;  // generated code
    c_wen = 1'b0;  // generated code
    v_wen = 1'b0;  // generated code
    kernel_op = 1'b0;  // generated code
    flag_op = 1'b0;  // generated code
    bcc = 1'b0;  // generated code
    link = 1'b0;  // generated code
    brcc_bbit = 1'b0;  // generated code
    cache_byp = 1'b0;  // generated code
    slow_op = 1'b0;  // generated code
    fast_op = 1'b0;  // generated code
    div_op = 1'b0;  // generated code
    btab_op = 1'b0;  // generated code
    ei_op = 1'b0;  // generated code
    in_eslot = 1'b0;  // generated code
    rel_branch = 1'b0;  // generated code
    illegal_operand = 1'b0;  // generated code
    swap_op = 1'b0;  // generated code
    setcc_op = 1'b0;  // generated code
    cc_field = 3'b0;  // generated code
    q_field = 5'b0;  // generated code
    dest_cr_is_ext = 1'b0;  // generated code
    add_op = 1'b0;  // generated code
    and_op = 1'b0;  // generated code
    or_op = 1'b0;  // generated code
    xor_op = 1'b0;  // generated code
    mov_op = 1'b0;  // generated code
    with_carry = 1'b0;  // generated code
    simple_shift_op = 1'b0;  // generated code
    left_shift = 1'b0;  // generated code
    rotate_op = 1'b0;  // generated code
    inv_src1 = 1'b0;  // generated code
    inv_src2 = 1'b0;  // generated code
    bit_op = 1'b0;  // generated code
    mask_op = 1'b0;  // generated code
    src2_mask_sel = 1'b0;  // generated code
    uop_commit = 1'b0;  // generated code
    uop_epil = 1'b0;  // generated code
    uop_excpn = 1'b0;  // generated code
    predicate = 1'b0;  // generated code
    rf_renb0 = 1'b0;  // generated code
    rf_renb1 = 1'b0;  // generated code
    rf_renb0_64 = 1'b0;  // generated code
    rf_renb1_64 = 1'b0;  // generated code
    rf_ra0 = 6'b0;  // generated code
    rf_ra1 = 6'b0;  // generated code
    jli_src0 = 1'b0;  // generated code
    uop_inst = 1'b0;  // generated code
    vec_shimm = 1'b0;  // generated code
    iprot_viol = 1'b0;  // generated code
    dmb_op = 1'b0;  // generated code
    dmb_type = 3'b0;  // generated code
    force_cin = 1'b0;  // generated code
    opd3_sel = 1'b0;  // generated code
    multi_op = 1'b0;  // generated code
    abs_op = 1'b0;  // generated code
    min_op = 1'b0;  // generated code
    max_op = 1'b0;  // generated code
    norm_op = 1'b0;  // generated code
    ldi_src0 = 1'b0;  // generated code
    pre_addr = 1'b0;  // generated code
    stimm_op = 1'b0;  // generated code
    src2_sh1 = 1'b0;  // generated code
    src2_sh2 = 1'b0;  // generated code
    src2_sh3 = 1'b0;  // generated code
    barrel_shift_op = 1'b0;  // generated code
    opds_in_x1 = 1'b0;  // generated code
    agu_uses_r0 = 1'b0;  // generated code
    opds_in_sa = 1'b0;  // generated code
    limm0_64 = 1'b0;  // generated code
    limm1_64 = 1'b0;  // generated code
    may_graduate = 1'b0;  // generated code
    agu_uses_r1 = 1'b0;  // generated code
    reads_acc = 1'b0;  // generated code
    dsync_op = 1'b0;  // generated code
    src2_shifts = 1'b0;  // generated code
    sel_shimm = 1'b0;  // generated code
    shimm = 32'b0;  // generated code
    limm_r0 = 1'b0;  // generated code
    limm_r1 = 1'b0;  // generated code
    offset = 32'b0;  // generated code


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
  

  case ( inst[31:27] )
  `npuarc_GRP_BRANCH_32:
    case ( inst[16] )
    1'b0: begin
            av2_inst = 1'b1;
            bcc           = 1'b1;
            rel_branch    = 1'b1;
            dslot         = inst[5];
            offset        = { {11{inst[15]}}, inst[15:6], inst[26:17], 1'b0 };
            begin
              q_field   = inst[4:0];
            end
            
          end
          
    1'b1: begin
            av2_inst = 1'b1;
            bcc           = 1'b1;
            rel_branch    = 1'b1;
          
            // q_field[4] is always 0 for non-extension instructions
            //
            q_field[3:0]  = 4'b0000;  // branch always
          
            dslot         = inst[5];
            offset        = { {7{inst[3]}}, inst[3:0], inst[15:6], inst[26:17], 1'b0 };
          end
          
    endcase

  `npuarc_GRP_BL_BRCC_32:
    case ( inst[16] )
    1'b0:
      case ( inst[17] )
      1'b0: begin
              av2_inst = 1'b1;
              bcc        = 1'b1;
              rel_branch = 1'b1;
              begin
                q_field   = inst[4:0];
              end
                      // branch according CC
              link       = 1'b1;
              mov_op     = 1'b1;      // to move link address from src2 to primary result
              fast_op    = 1'b1;      // link value gets computed in 1 cycle
              rf_wa0     = 6'd31;     // BLINK register
              rf_wenb0   = 1'b1;      // which gets written if branch taken
              dslot      = inst[5];
              offset     = { {11{inst[15]}}, inst[15:6], inst[26:18], 2'b00 };
            end
            
      1'b1: begin
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
            
      endcase
    1'b1:
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
        1'b0: begin
                begin
                end
                
              
              end
              
        1'b1: begin                     // for source operands only
                begin                     // source operand only
                  shimm     = { 26'd0, inst[11:6] };
                  sel_shimm = 1'b1;
                end
                
              end
              
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
      
    endcase

  `npuarc_GRP_LOAD_32:
    begin
    begin
      // Extract field 'a' from a 32-bit inst
      // where 'a' is destination of a Load operation
      rf_wa1 = inst[5:0];
      rf_wenb1 = (inst[5:0] != 6'd62);
    end
      // destination register
    begin
    end
       // source register
    begin
      av2_inst  = 1'b1;
      load      = 1'b1;
      shimm     = { {24{inst[15]}}, inst[23:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    
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
         // literal and control actions
    end

  `npuarc_GRP_STORE_32:
    begin
    begin                     // EC5 requires that J or JL also sets opd3_sel
    end
       // source register
    begin
    end
       // source register
    begin
      av2_inst = 1'b1;
      store = 1'b1;
      opd3_sel = 1'b1;
      shimm = { {24{inst[15]}}, inst[23:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    
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
        // literal and control actions
    end

  `npuarc_GRP_BASECASE_32:
    begin
    if (inst[21:19] == `npuarc_LD_RR_FMT)
      begin
      begin
        av2_inst  = 1'b1;
        load      = 1'b1;
        signed_op = inst[16];
        cache_byp = inst[15];
        begin                     // where operation is a Load writing to write port 1
          begin
            // Extract field 'a' from a 32-bit inst
            // where 'a' is destination of a Load operation
            rf_wa1 = inst[5:0];
            rf_wenb1 = (inst[5:0] != 6'd62);
          end
          
          begin
            begin
            end
            
          
          end
          
          begin
            flag_enable = inst[15];
          end
          
        end
        
        begin
          av2_inst = 1'b1;
          add_op  = 1'b1;         // perform 2'c complement addition
          fast_op = 1'b1;         // allow next-cycle forwarding of result
        end
        
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
      
      end
    else
      begin
      // Firstly, decode the operand format
      case ( inst[23:22])
      `npuarc_REG_REG_FMT: // REG_REG format for major opcode 0x04
        case (inst[21:16])
        // firstly all exceptions are listed
        `npuarc_AEX_OP,
        `npuarc_MOV_OP,
        `npuarc_LR_OP:     begin
                      rf_wa0        = { inst[14:12], inst[26:24] };
                      rf_wenb0      = ({inst[14:12], inst[26:24]} != 6'd62);
                    end
                     // mov or lr reg-reg

        `npuarc_SR_OP,
        `npuarc_TST_OP,
        `npuarc_BTST_OP,
        `npuarc_CMP_OP,
        `npuarc_RCMP_OP:   begin
                      begin
                      end
                      
                    
                    end
                         // source regs only

        `npuarc_BI_OP,
        `npuarc_BIH_OP,
        `npuarc_LDI_OP,
        `npuarc_FLAG_OP,
        `npuarc_JCC_OP,
        `npuarc_JCC_D_OP,
        `npuarc_JLCC_OP,
        `npuarc_JLCC_D_OP: begin                     // EC5 requires that J or JL also sets opd3_sel
                    end
                          // J/JL [c]

        `npuarc_SOP_FMT:
        begin
          if (inst[5:0] == `npuarc_ZOP_FMT)        // Sleep: no write
            begin
              rf_wenb0 = 1'b0;
            end
            
          else
            begin
              rf_wa0    = { inst[14:12], inst[26:24] };
              rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
              begin
                flag_enable = inst[15];
              end
              
            end
                     // SOP b,[c|limm]
        end

        `npuarc_LPCC_OP:   begin
                      // raise an Illegal Instruction exception
                      illegal_instr = 1'b1;
                    end
                           // LPcc disallowed

        // secondly, the default operands are extracted
        default:    begin
                      begin
                        // Extract field 'a' from a 32-bit inst where
                        // 'a' is destination of non-Load operation
                        rf_wa0 = inst[5:0];
                        rf_wenb0 = (inst[5:0] != 6'd62);
                      end
                      
                      begin
                        begin
                        end
                        
                      
                      end
                      
                      begin
                        flag_enable = inst[15];
                      end
                      
                    end
                      // Generic reg-reg
        endcase

      `npuarc_REG_U6IMM_FMT: // REG_U6IMM format for major opcode 0x04
        begin
          case (inst[21:16])
          // firstly all exceptions are listed
          `npuarc_AEX_OP,
          `npuarc_MOV_OP,
          `npuarc_LR_OP:     begin
                        rf_wa0    = { inst[14:12], inst[26:24] };
                        rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
                        shimm     = { 26'd0, inst[11:6] };
                        sel_shimm = 1'b1;
                      end
                         // mov or lr reg-u6

          `npuarc_SR_OP,
          `npuarc_TST_OP,
          `npuarc_BTST_OP,
          `npuarc_CMP_OP,
          `npuarc_RCMP_OP:   begin                     // for source operands only
                        begin                     // source operand only
                          shimm     = { 26'd0, inst[11:6] };
                          sel_shimm = 1'b1;
                        end
                        
                      end
                             // source b,u6 only

          `npuarc_LDI_OP,
          `npuarc_JCC_OP,
          `npuarc_JCC_D_OP,
          `npuarc_JLCC_OP,
          `npuarc_JLCC_D_OP,
          `npuarc_FLAG_OP:   begin                     // source operand only
                        shimm     = { 26'd0, inst[11:6] };
                        sel_shimm = 1'b1;
                      end
                      

          `npuarc_SOP_FMT:
          begin
          if (inst[5:0] == `npuarc_ZOP_FMT)        // Sleep: no write
            begin
              rf_wenb0 = 1'b0;
            end
            
          else
            begin
              rf_wa0    = { inst[14:12], inst[26:24] };
              rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
              shimm     = { 26'd0, inst[11:6] };
              sel_shimm = 1'b1;
              begin
                flag_enable = inst[15];
              end
              
            end
               // SOP b,u6
          end

          `npuarc_LPCC_OP:   begin
                        offset  = { 25'd0, inst[11:6], 1'd0 };
                      end
                              // ucond LP u7

          `npuarc_BI_OP,
          `npuarc_BIH_OP:    begin
                        // raise an Illegal Instruction exception
                        illegal_instr = 1'b1;
                      end
                                // BI, BIH disallowed

          // secondly, the default operands are extracted
          default:    begin
                        begin
                          // Extract field 'a' from a 32-bit inst where
                          // 'a' is destination of non-Load operation
                          rf_wa0 = inst[5:0];
                          rf_wenb0 = (inst[5:0] != 6'd62);
                        end
                        
                        begin                     // for source operands only
                          begin                     // source operand only
                            shimm     = { 26'd0, inst[11:6] };
                            sel_shimm = 1'b1;
                          end
                          
                        end
                        
                        begin
                          flag_enable = inst[15];
                        end
                        
                      end
                            // Generic reg-u6
          endcase
          sel_shimm = 1'b1; // source 2 is always short-immediate
        end
        
      `npuarc_REG_S12IMM_FMT:  // REG_S12IMM format for major opcode 0x04
        begin
          case (inst[21:16])
          // firstly all exceptions are listed
          `npuarc_MOV_OP,
          `npuarc_LR_OP:     begin
                        rf_wa0    = { inst[14:12], inst[26:24] };
                        rf_wenb0  = ({ inst[14:12], inst[26:24] } != 6'd62);
                        begin
                          shimm     = { {20{inst[5]}}, inst[5:0], inst[11:6] };
                          sel_shimm = 1'b1;
                        end
                        
                        begin
                          flag_enable = inst[15];
                        end
                        
                      end
                           // SOP, mov or lr reg-s12

          `npuarc_SR_OP,
          `npuarc_TST_OP,
          `npuarc_BTST_OP,
          `npuarc_CMP_OP,
          `npuarc_RCMP_OP:   begin
                        begin
                          shimm     = { {20{inst[5]}}, inst[5:0], inst[11:6] };
                          sel_shimm = 1'b1;
                        end
                        
                        begin
                          flag_enable = inst[15];
                        end
                        
                      end
                            // source b,s12 only

          `npuarc_LDI_OP,
          `npuarc_FLAG_OP,
          `npuarc_JCC_OP,
          `npuarc_JCC_D_OP,
          `npuarc_JLCC_OP,
          `npuarc_JLCC_D_OP: begin
                        shimm     = { {20{inst[5]}}, inst[5:0], inst[11:6] };
                        sel_shimm = 1'b1;
                      end
                             // J/JL s12

          `npuarc_LPCC_OP:   begin
                        offset = { {19{inst[5]}}, inst[5:0], inst[11:6], 1'd0 };
                      end
                           // ucond LP s13

          `npuarc_SOP_FMT:   begin
                        // raise an Illegal Instruction exception
                        illegal_instr = 1'b1;
                      end
                                // SOP_FMT disallowed
          `npuarc_BI_OP,
          `npuarc_BIH_OP:    begin
                        // raise an Illegal Instruction exception
                        illegal_instr = 1'b1;
                      end
                                // BI, BIH disallowed

          // secondly, the default operands are extracted
          default:    begin                       // as well as field 's12' from a 32-bit inst.
                        rf_wa0    = { inst[14:12], inst[26:24] };
                        rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
                        begin
                          begin
                            shimm     = { {20{inst[5]}}, inst[5:0], inst[11:6] };
                            sel_shimm = 1'b1;
                          end
                          
                          begin
                            flag_enable = inst[15];
                          end
                          
                        end
                        
                      end
                           // Generic reg-s12
          endcase
          sel_shimm = 1'b1; // source 2 is always short-immediate
        end

      `npuarc_REG_COND_FMT:  // REG_COND format for major opcode 0x04
        begin
        case (inst[21:16])
        // firstly all exceptions are listed
        `npuarc_SOP_FMT,                        // SOP format disallowed
        `npuarc_LDI_OP,
        `npuarc_LR_OP,                          // LR disallowed
        `npuarc_SR_OP:     begin
                      // raise an Illegal Instruction exception
                      illegal_instr = 1'b1;
                    end
                        // SR disallowed

        `npuarc_TST_OP,
        `npuarc_BTST_OP,
        `npuarc_CMP_OP,
        `npuarc_RCMP_OP:
          begin
            begin
            end
            
            begin
              q_field   = inst[4:0];
            end
            
            case (inst[5])
            1'b0: begin                     // EC5 requires that J or JL also sets opd3_sel
                  end
                  
            1'b1: begin                     // source operand only
                    shimm     = { 26'd0, inst[11:6] };
                    sel_shimm = 1'b1;
                  end
                  
            endcase
          end

        `npuarc_FLAG_OP,
        `npuarc_JCC_OP,
        `npuarc_JCC_D_OP,
        `npuarc_JLCC_OP,
        `npuarc_JLCC_D_OP:
          begin
            begin
              q_field   = inst[4:0];
            end
            
            case (inst[5])
            1'b0: begin                     // EC5 requires that J or JL also sets opd3_sel
                  end
                  
            1'b1: begin                     // source operand only
                    shimm     = { 26'd0, inst[11:6] };
                    sel_shimm = 1'b1;
                  end
                  
            endcase
          end

        `npuarc_LPCC_OP:   begin
                      offset  = { 25'd0, inst[11:6], 1'd0 };
                      begin
                        q_field   = inst[4:0];
                      end
                      
                      illegal_instr = !inst[5];
                    end
                    

        `npuarc_BI_OP,
        `npuarc_BIH_OP:    begin
                      // raise an Illegal Instruction exception
                      illegal_instr = 1'b1;
                    end
                              // BI, BIH disallowed

        // secondly, the default operands are extracted
        default:  begin
            begin
              rf_wa0   = { inst[14:12], inst[26:24] };
              rf_wenb0 = ({ inst[14:12], inst[26:24] } != 6'd62);
            
              begin                     // for source operands only
                                                              begin
                                                              end
                                                              
                                                              begin
                                                                q_field   = inst[4:0];
                                                              end
                                                              
                                                              begin
                                                                flag_enable = inst[15];
                                                              end
                                                              
                                                            end
                                                            
            end
                // Generic reg-cond
            case (inst[5])
            1'b0: begin                     // EC5 requires that J or JL also sets opd3_sel
                  end
                  
            1'b1: begin                     // source operand only
                    shimm     = { 26'd0, inst[11:6] };
                    sel_shimm = 1'b1;
                  end
                  
            endcase
            end
        // take care of Section 4.9.9.1
        endcase
        end
      endcase

      // Secondly, decode the operator
      case ( inst[21:16] )
      `npuarc_ADD_OP:   begin
                   av2_inst = 1'b1;
                   add_op  = 1'b1;         // perform 2'c complement addition
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                   c_write = 1'b1;
                   v_write = 1'b1;
                 end
                 
      `npuarc_ADC_OP:   begin
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
                 
      `npuarc_SUB_OP:   begin
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
                 
      `npuarc_SBC_OP:   begin
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
                 
      `npuarc_AND_OP:   begin
                   av2_inst = 1'b1;
                   and_op = 1'b1;          // perform dst = src1 & src2
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                 end
                 
      `npuarc_OR_OP:    begin
                   av2_inst = 1'b1;
                   or_op = 1'b1;           // perform logical OR
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                 end
                 
      `npuarc_BIC_OP:   begin
                   av2_inst = 1'b1;
                   and_op   = 1'b1;        // perform dst = src1 & ~src2
                   fast_op  = 1'b1;        // allow next-cycle forwarding of result
                   inv_src2 = 1'b1;
                   z_write  = 1'b1;
                   n_write  = 1'b1;
                 end
                 
      `npuarc_XOR_OP:   begin
                   av2_inst = 1'b1;
                   xor_op = 1'b1;          // perform logical AND
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                 end
                 
      `npuarc_MAX_OP:   begin
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
                 
      `npuarc_MIN_OP:   begin
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
                 
      `npuarc_MOV_OP:   begin
                   av2_inst = 1'b1;
                   mov_op   = 1'b1;        // MOV src2 to dst
                   fast_op  = 1'b1;        // allow next-cycle forwarding of result
                   begin
                     flag_enable = inst[15];
                   end
                             // detect mov.f instruction
                   z_write  = 1'b1;        //  - enable Z update if mov.f
                   n_write  = 1'b1;        //  - enable N update if mov.f
                 end
                 
      `npuarc_TST_OP:   begin
                   av2_inst = 1'b1;
                   rf_wenb0 = 1'b0;        // disable destination write
                   and_op = 1'b1;          // perform bit-wise AND
                   z_write = 1'b1;
                   n_write = 1'b1;
                   flag_enable = 1'b1;     // tst and tst_s always update flags
                   fast_op = 1'b1;         // flag result available after 1 cycle
                 
                   if (inst[15] == 1'b0)   // TST must have bit 15 set to 1
                     begin
                       // raise an Illegal Instruction exception
                       illegal_instr = 1'b1;
                     end
                     
                 end
                 
      `npuarc_CMP_OP:   
          if (inst[15] == 1'b1)
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
            
          else
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
                begin
                  // raise an Illegal Instruction exception
                  illegal_instr = 1'b1;
                end
                
            end
            
      `npuarc_RCMP_OP:
          if (inst[15] == 1'b1)
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
            
          else
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
                begin
                  // raise an Illegal Instruction exception
                  illegal_instr = 1'b1;
                end
                
            end
            
      `npuarc_RSUB_OP:  begin
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
                 
      `npuarc_BSET_OP:  begin
                   av2_inst = 1'b1;
                   or_op = 1'b1;           // perform logical OR
                   bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
                   src2_mask_sel = 1'b1;   // select mask in operand stage
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                   fast_op = 1'b1;         // flag result available after 1 cycle
                 end
                 
      `npuarc_BCLR_OP:  begin
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
                 
      `npuarc_BTST_OP:  begin
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
                     begin
                       // raise an Illegal Instruction exception
                       illegal_instr = 1'b1;
                     end
                     
                 end
                 
      `npuarc_BXOR_OP:  begin
                   av2_inst = 1'b1;
                   xor_op = 1'b1;          // perform logical XOR
                   bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
                   src2_mask_sel = 1'b1;   // select mask in operand stage
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                 end
                 
      `npuarc_BMSK_OP:  begin
                   av2_inst = 1'b1;
                   and_op = 1'b1;          // perform logical AND
                   mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
                   src2_mask_sel = 1'b1;   // select mask in operand stage
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                 end
                 
      `npuarc_ADD1_OP:  begin
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
                 
      `npuarc_ADD2_OP:  begin
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
                 
      `npuarc_ADD3_OP:  begin
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
                 
      `npuarc_SUB1_OP:  begin
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
                 
      `npuarc_SUB2_OP:  begin
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
                 
      `npuarc_SUB3_OP:  begin
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
                 
      `npuarc_MPYLO_OP: begin
                   av2_inst = 1'b1;
                    mpy_op     = 1'b1;
                    signed_op  = 1'b1;
                    z_write    = 1'b1;
                    n_write    = 1'b1;
                    v_write    = 1'b1;
                 end
                 
      `npuarc_MPYHI_OP: begin
                   av2_inst = 1'b1;
                    mpy_op     = 1'b1;
                    byte_size  = 1'b1;       // selects upper 32-bits of result
                    signed_op  = 1'b1;
                    z_write    = 1'b1;
                    n_write    = 1'b1;
                    v_write    = 1'b1;
                 end
                 
      `npuarc_MPYHIU_OP:begin
                   av2_inst = 1'b1;
                    mpy_op     = 1'b1;
                    byte_size  = 1'b1;       // selects upper 32-bits of result
                    z_write    = 1'b1;
                    n_write    = 1'b1;
                    v_write    = 1'b1;
                 end
                 
      `npuarc_MPYLOU_OP:begin
                   av2_inst = 1'b1;
                    mpy_op     = 1'b1;
                    z_write    = 1'b1;
                    n_write    = 1'b1;
                    v_write    = 1'b1;
                 end
                 
      `npuarc_MPYW_OP:  begin
                   av2_inst = 1'b1;
                    mpy_op     = 1'b1;
                    half_size  = 1'b1;
                    signed_op  = 1'b1;
                    z_write    = 1'b1;
                    n_write    = 1'b1;
                    v_write    = 1'b1;
                 end
                 
      `npuarc_MPYUW_OP: begin
                   av2_inst = 1'b1;
                    mpy_op     = 1'b1;
                    half_size  = 1'b1;
                    z_write    = 1'b1;
                    n_write    = 1'b1;
                    v_write    = 1'b1;
                 end
                 
      `npuarc_JCC_D_OP,
      `npuarc_JCC_OP:   begin
                   av2_inst = 1'b1;
                   jump     = 1'b1;        // select jump functionality
                   dslot    = inst[16];
                   if ((dslot == 1'b1) && (limm_r1 == 1'b1))
                   begin
                     begin
                       // raise an Illegal Instruction exception
                       illegal_instr = 1'b1;
                     end
                     
                   end
                   opd3_sel = 1'b1;        // target is always via src2 operand
                 end
                 
      `npuarc_JLCC_D_OP,
      `npuarc_JLCC_OP:  begin
                   av2_inst = 1'b1;
                   mov_op   = 1'b1;        // to move link address from src2 to primary result
                   jump     = 1'b1;        // select jump functionality
                   link     = 1'b1;
                   rf_wa0   = 6'd31;       // BLINK register
                   rf_wenb0 = 1'b1;        // which gets written if jump is taken
                   dslot    = inst[16];
                   if ((dslot == 1'b1) && (limm_r1 == 1'b1))
                   begin
                     begin
                       // raise an Illegal Instruction exception
                       illegal_instr = 1'b1;
                     end
                     
                   end
                   opd3_sel = 1'b1;        // target is always via src2 operand
                   fast_op  = 1'b1;        // link value available immediately
                 end
                 
      `npuarc_BI_OP,
      `npuarc_BIH_OP:   begin
                   av2_inst = 1'b1;
                   if (inst[15] == 1'b1)   // the <.f> bit must be zero
                     begin
                       // raise an Illegal Instruction exception
                       illegal_instr = 1'b1;
                     end
                     
                 
                   src2_sh2   = ~inst[16]; // BI  operation shifts [c] 2 places
                   src2_sh1   =  inst[16]; // BIH operation shifts [c] 1 place
                   add_op     = 1'b1;         // add PC and (c << 1 or 2)
                   btab_op    = 1'b1;         // ucode for BI and BIH
                   opds_in_sa = 1'b1;      // must have operands in SA stage
                 end
                 
      // CD2_OPTION start
      `npuarc_LDI_OP:   begin
                   av2_inst   = 1'b1;
                   load       = 1'b1;
                   ldi_src0   = 1'b1; // select LDI_BASE aux register as src0
                   src2_sh2   = 1'b1; // table index is always scaled by 4
                   rf_wa1     = { inst[14:12], inst[26:24] };
                   rf_wenb1   = ({inst[14:12], inst[26:24]} != 6'd62);
                 end
                 
      // CD2_OPTION end
      `npuarc_AEX_OP:   begin
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
                 
      `npuarc_LPCC_OP:  begin
                   av2_inst = 1'b1;
                   loop_op    = 1'b1;      // tell datapath we're doing an LPcc
                   rel_branch = 1'b1;      // lp_end needs relative offset + PC
                   opds_in_sa = 1'b1;
                 end                       // format decode gets the rest...
                 
      `npuarc_FLAG_OP:  begin                     // or halt processor if H-bit set
                   av2_inst        = 1'b1;
                   flag_op         = 1'b1;
                   cache_byp       = inst[15];   // indicates a kflag operation
                   opds_in_sa      = 1'b1;
                 end
                 
      `npuarc_LR_OP:    begin
                   av2_inst      = 1'b1;
                   lr_op         = 1'b1;
                   opds_in_sa    = 1'b1;
                 end
                 
      `npuarc_SR_OP:    begin
                   av2_inst       = 1'b1;
                   sr_op          = 1'b1;
                   opds_in_sa     = 1'b1;
                   opd3_sel       = 1'b1;
                 end
                 
      `npuarc_BMSKN_OP: begin
                   av2_inst = 1'b1;
                   and_op = 1'b1;          // perform logical AND
                   mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
                   src2_mask_sel = 1'b1;   // select mask in operand stage
                   inv_src2 = 1'b1;        // invert the bit mask
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   n_write = 1'b1;
                 end
                 
      `npuarc_XBFU_OP:  begin
                   av2_inst = 1'b1;
                   barrel_shift_op = 1'b1; // select barrel shifter
                   mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
                   src2_mask_sel = 1'b1;   // select mask in operand stage
                   fast_op = 1'b1;         // allow next-cycle forwarding of result
                   z_write = 1'b1;
                   opds_in_sa = 1'b1;      // force execution in early ALU
                 end
                 
      `npuarc_SOP_FMT: // All Single or Zero operand 32-bit insns
        begin
        case ( inst[5:0] )
        `npuarc_ASL_OP:  begin
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
                  
        `npuarc_ASR_OP:  begin
                    av2_inst = 1'b1;
                    simple_shift_op = 1'b1; // select logic unit shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    signed_op = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                    c_write = 1'b1;
                  end
                  
        `npuarc_LSR_OP:  begin
                    av2_inst = 1'b1;
                    simple_shift_op = 1'b1; // select logic unit shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    z_write = 1'b1;
                    n_write = 1'b1;
                    c_write = 1'b1;
                  end
                  
        `npuarc_ROR_OP:  begin
                    av2_inst = 1'b1;
                    simple_shift_op = 1'b1; // select logic unit shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    rotate_op = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                    c_write = 1'b1;
                  end
                  
        `npuarc_RRC_OP:  begin
                    av2_inst = 1'b1;
                    simple_shift_op = 1'b1; // select logic unit shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    rotate_op = 1'b1;
                    with_carry = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                    c_write = 1'b1;
                  end
                  
        `npuarc_SEXB_OP: begin
                    av2_inst = 1'b1;
                    mov_op = 1'b1;
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    byte_size = 1'b1;
                    signed_op = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                  end
                  
        `npuarc_SEXW_OP: begin
                    av2_inst = 1'b1;
                    mov_op = 1'b1;
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    half_size = 1'b1;
                    signed_op = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                  end
                  
        `npuarc_EXTB_OP: begin
                    av2_inst = 1'b1;
                    mov_op = 1'b1;
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    byte_size = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                  end
                  
        `npuarc_EXTW_OP: begin
                    av2_inst = 1'b1;
                    mov_op = 1'b1;
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    half_size = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                  end
                  
        `npuarc_ABS_OP:  begin
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
                  
        `npuarc_NOT_OP:  begin
                    av2_inst = 1'b1;
                    xor_op = 1'b1;
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    inv_src1 = 1'b1;        // compute ~(0) ^ src
                    z_write = 1'b1;
                    n_write = 1'b1;
                  end
                  
        `npuarc_RLC_OP:  begin
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
                  
        `npuarc_ROL_OP:  begin
                    av2_inst = 1'b1;
                    simple_shift_op = 1'b1; // select logic unit shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    rotate_op = 1'b1;
                    left_shift = 1'b1;
                    z_write = 1'b1;
                    n_write = 1'b1;
                    c_write = 1'b1;
                  end
                  
        `npuarc_EX_OP:   begin
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
                  
        `npuarc_LDDL_OP,
        `npuarc_LDL_OP:  begin
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
                  
        `npuarc_STDC_OP,
        `npuarc_STC_OP:  begin
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
                  
        `npuarc_ZOP_FMT: // All zero-operand 32-bit insns
          begin
          case ( {inst[14:12], inst[26:24]} )
          `npuarc_WEVT_OP,
          `npuarc_WLFC_OP,
          `npuarc_SLEEP_OP: begin
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
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       opds_in_sa = 1'b1;
                     end
                     
          `npuarc_SWI_OP:   begin
                       av2_inst = 1'b1;
                       flag_enable = 1'b0;  // swi does not affect the ZNCV flags
                       trap_op     = 1'b1;  // uses trap_op ucode, with byte_size == 0
                       begin
                         rf_wenb0 = 1'b0;
                       end
                       
                     
                       // SWI requires bit 15 to be 0
                       if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       opds_in_sa = 1'b1;
                     end
                     
          
          `npuarc_DSYNC_OP,
          `npuarc_DMB_OP,
          `npuarc_SYNC_OP:  begin
                       av2_inst  = 1'b1;
                       sync_op   = ~inst[12]; // excludes DSYNC and DMB
                       dsync_op  = inst[12] & (~inst[24]);
                       dmb_op    = inst[12] &  inst[24];
                       dmb_type  = inst[8:6];
                       begin
                         rf_wenb0 = 1'b0;
                       end
                       
                     
                       if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       
                     end
                     
          
          `npuarc_RTIE_OP:  begin
                       av2_inst  = 1'b1;
                       kernel_op = 1'b1;       // Kernel-only instruction
                       opd3_sel  = 1'b0;
                       sel_shimm = 1'b0;
                       multi_op  = 1'b1;
                       begin
                         rf_wenb0 = 1'b0;
                       end
                       
                     
                       if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       else
                         rtie_op   = 1'b1;
                     
                       opds_in_sa = 1'b1;
                     end
                     
          `npuarc_BRK_OP:   begin
                       av2_inst = 1'b1;
                       kernel_op = !aux_dbg_ub_r;  // Kernel op when DEBUG.UB == 0
                       begin
                         rf_wenb0 = 1'b0;
                       end
                       
                       // BRK requires bit 15 to be 0
                       if ((inst[15] == 1'b1) || (inst[23:22] == 2'b00))
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       else
                         brk_op    = 1'b1;
                     
                       opds_in_sa = 1'b1;
                     end
                     
          `npuarc_SETI_OP:  begin
                       av2_inst   = 1'b1;
                       begin
                         rf_wenb0 = 1'b0;
                       end
                       
                     
                       flag_op    = 1'b1;
                       cache_byp  = 1'b1;
                       kernel_op  = 1'b1;
                     
                       // Identify as SETI/CLRI
                       signed_op  = 1'b1;
                     
                       shimm      = { 26'd0, inst[11:6] };
                       sel_shimm  = inst[22];
                     
                       if (inst[15] == 1'b1)
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       opds_in_sa = 1'b1;
                     end
                     
          `npuarc_CLRI_OP:  begin
                       av2_inst  = 1'b1;
                       flag_op   = 1'b1;
                       cache_byp = 1'b0;
                       kernel_op = 1'b1;
                       rf_wa0    = inst[11:6];
                       rf_wenb0  = (inst[23:22] == 2'b00) & (rf_wa0 != 6'd62);
                       // Identify as SETI/CLRI
                       signed_op = 1'b1;
                     
                       if (inst[15] == 1'b1)
                         begin
                           // raise an Illegal Instruction exception
                           illegal_instr = 1'b1;
                         end
                         
                       opds_in_sa = 1'b1;
                     end
                     
          default: begin
                     // will be an illegal inst, unless EIA instruction matches
                     av2_inst = 1'b0;
                   end
                   
          endcase
          end
        default: begin
                   // will be an illegal inst, unless EIA instruction matches
                   av2_inst = 1'b0;
                 end
                 
        endcase
        end
      `npuarc_SETEQ_OP, `npuarc_SETNE_OP, `npuarc_SETLT_OP, `npuarc_SETGE_OP,
      `npuarc_SETLO_OP, `npuarc_SETHS_OP, `npuarc_SETLE_OP, `npuarc_SETGT_OP:
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
        
      default: begin
                 // will be an illegal inst, unless EIA instruction matches
                 av2_inst = 1'b0;
               end
               
      endcase
      end
    end

  `npuarc_GRP_ARC_EXT0_32:
    begin
      // Firstly, decode the operand format in the same
      // way as GRP_BASECASE_32, but without the exceptional
      // formats that appear in the basecase group
      //
      case ( inst[23:22])
      `npuarc_REG_REG_FMT:     // REG_REG format for major opcode 0x05
        case (inst[21:16])
        // first specify all the exceptions
        `npuarc_SOP_FMT:   begin
                      rf_wa0    = { inst[14:12], inst[26:24] };
                      rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
                      begin
                        flag_enable = inst[15];
                      end
                      
                    end
                      // SOP b,[c|limm]
        // secondly, the default operands are extracted
        default:    begin
                      begin
                        // Extract field 'a' from a 32-bit inst where
                        // 'a' is destination of non-Load operation
                        rf_wa0 = inst[5:0];
                        rf_wenb0 = (inst[5:0] != 6'd62);
                      end
                      
                      begin
                        begin
                        end
                        
                      
                      end
                      
                      begin
                        flag_enable = inst[15];
                      end
                      
                    end
                         // Generic reg-reg
        endcase

      `npuarc_REG_U6IMM_FMT:   // REG_U6IMM format for major opcode 0x05
        begin
          case (inst[21:16])
          // first specify all the exceptions
          `npuarc_SOP_FMT:   begin
                        rf_wa0    = { inst[14:12], inst[26:24] };
                        rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
                        shimm     = { 26'd0, inst[11:6] };
                        sel_shimm = 1'b1;
                        begin
                          flag_enable = inst[15];
                        end
                        
                      end
                       // SOP b,u6
          // secondly, the default operands are extracted
          default:    begin
                        begin
                          // Extract field 'a' from a 32-bit inst where
                          // 'a' is destination of non-Load operation
                          rf_wa0 = inst[5:0];
                          rf_wenb0 = (inst[5:0] != 6'd62);
                        end
                        
                        begin                     // for source operands only
                          begin                     // source operand only
                            shimm     = { 26'd0, inst[11:6] };
                            sel_shimm = 1'b1;
                          end
                          
                        end
                        
                        begin
                          flag_enable = inst[15];
                        end
                        
                      end
                          // Generic reg-u6
          endcase
          sel_shimm = 1'b1; // source 2 is always short-immediate
        end

      `npuarc_REG_S12IMM_FMT:  // REG_S12IMM format for major opcode 0x05
        begin
          case (inst[21:16])
          // first specify all the exception
          `npuarc_SOP_FMT:   begin
                        // raise an Illegal Instruction exception
                        illegal_instr = 1'b1;
                      end
                              // SOP_FMT disallowed
          default:    begin                       // as well as field 's12' from a 32-bit inst.
                        rf_wa0    = { inst[14:12], inst[26:24] };
                        rf_wenb0  = ({inst[14:12], inst[26:24]} != 6'd62);
                        begin
                          begin
                            shimm     = { {20{inst[5]}}, inst[5:0], inst[11:6] };
                            sel_shimm = 1'b1;
                          end
                          
                          begin
                            flag_enable = inst[15];
                          end
                          
                        end
                        
                      end
                         // Generic reg-s12
          endcase
          sel_shimm = 1'b1; // source 2 is always short-immediate
        end

      `npuarc_REG_COND_FMT:    // REG_COND format for major opcode 0x05
        begin
        case (inst[5])
        1'b0: begin                     // EC5 requires that J or JL also sets opd3_sel
              end
              
        1'b1: begin                     // source operand only
                shimm     = { 26'd0, inst[11:6] };
                sel_shimm = 1'b1;
              end
              
        endcase
        case (inst[21:16])
        // first list all the exceptions
        `npuarc_SOP_FMT:   begin
                      // raise an Illegal Instruction exception
                      illegal_instr = 1'b1;
                    end
                            // SOP_FMT disallowed
        default:    begin
                      rf_wa0   = { inst[14:12], inst[26:24] };
                      rf_wenb0 = ({ inst[14:12], inst[26:24] } != 6'd62);
                    
                      begin                     // for source operands only
                                                              begin
                                                              end
                                                              
                                                              begin
                                                                q_field   = inst[4:0];
                                                              end
                                                              
                                                              begin
                                                                flag_enable = inst[15];
                                                              end
                                                              
                                                            end
                                                            
                    end
                         // Generic reg-cond
        // take care of Section 4.9.9.1
        endcase
        end
      endcase

      // Secondly, decode the operator
      case ( inst[21:16] )
      `npuarc_ASLM_OP:   begin
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
                  
      `npuarc_LSRM_OP:   begin
                    av2_inst = 1'b1;
                    barrel_shift_op = 1'b1; // select barrel shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    z_write = 1'b1;         // logical right shift by default
                    n_write = 1'b1;
                    c_write = 1'b1;
                    opds_in_sa = 1'b1;      // force execution in early ALU
                  end
                  
      `npuarc_ASRM_OP:   begin
                    av2_inst = 1'b1;
                    barrel_shift_op = 1'b1; // select barrel shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    signed_op = 1'b1;       // arithmetic shift
                    z_write = 1'b1;         // right shift by default
                    n_write = 1'b1;
                    c_write = 1'b1;
                    opds_in_sa = 1'b1;      // force execution in early ALU
                  end
                  
      `npuarc_RORM_OP:   begin
                    av2_inst = 1'b1;
                    barrel_shift_op = 1'b1; // select barrel shifter
                    fast_op = 1'b1;         // allow next-cycle forwarding of result
                    rotate_op = 1'b1;       // rotate is selected
                    z_write = 1'b1;         // right shift by default
                    n_write = 1'b1;
                    c_write = 1'b1;
                    opds_in_sa = 1'b1;      // force execution in early ALU
                  end
                  
      `npuarc_DIV_OP:    begin
                    av2_inst = 1'b1;
                    div_op     = 1'b1;
                    signed_op  = 1'b1;
                    z_write    = 1'b1;  // set if quotient is zero
                    n_write    = 1'b1;  // set if quotient is negative
                    v_write    = 1'b1;  // set if operand 2 is zero
                  end
                  
      `npuarc_DIVU_OP:   begin
                    av2_inst = 1'b1;
                    div_op     = 1'b1;
                    z_write    = 1'b1;  // set if quotient is zero
                    n_write    = 1'b1;  // always cleared
                    v_write    = 1'b1;  // set if operand 2 is zero
                  end
                  
      `npuarc_REM_OP:    begin
                    av2_inst = 1'b1;
                    div_op     = 1'b1;
                    byte_size  = 1'b1;  // encodes rem operator within divide unit
                    signed_op  = 1'b1;
                    z_write    = 1'b1;  // set if remainder is zero
                    n_write    = 1'b1;  // set if remainder is negative
                    v_write    = 1'b1;  // set if operand 2 is zero
                  end
                  
      `npuarc_REMU_OP:   begin
                    av2_inst = 1'b1;
                    div_op     = 1'b1;
                    byte_size  = 1'b1;  // encodes rem operator within divide unit
                    z_write    = 1'b1;  // set if remainder is zero
                    n_write    = 1'b1;  // always cleared
                    v_write    = 1'b1;  // set if operand 2 is zero
                  end
                  
      `npuarc_MAC_OP:       {av2_inst,mpy_op,signed_op,acc_op,acc_wenb,n_write,v_write} = 7'b11111_11;
      `npuarc_MACU_OP:      {av2_inst,mpy_op,signed_op,acc_op,acc_wenb,n_write,v_write,macu} = 8'b11011_01_1;
      //
      `npuarc_DMPYH_OP:     {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,n_write,v_write} = 10'b11111011_11;
      `npuarc_DMPYHU_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,n_write,v_write} = 10'b11110011_01;
      `npuarc_DMACH_OP:     {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,n_write,v_write} = 10'b11111111_11;
      `npuarc_DMACHU_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,n_write,v_write} = 10'b11110111_01;
      //
      `npuarc_VADD2H_OP:    {av2_inst,add_op,vec_shimm,half_size,dual_op,vector_op,force_cin,inv_src2} = 8'b11111100;
      `npuarc_VSUB2H_OP:    {av2_inst,add_op,vec_shimm,half_size,dual_op,vector_op,force_cin,inv_src2} = 8'b11111111;
      `npuarc_VADDSUB2H_OP: {av2_inst,add_op,vec_shimm,half_size,dual_op,vector_op,force_cin,inv_src2} = 8'b11111110;
      `npuarc_VSUBADD2H_OP: {av2_inst,add_op,vec_shimm,half_size,dual_op,vector_op,force_cin,inv_src2} = 8'b11111101;      
      `npuarc_MPYD_OP:      {av2_inst,mpy_op,signed_op,acc_op,acc_wenb,n_write,v_write} = 7'b11101_11;
      `npuarc_MPYDU_OP:     {av2_inst,mpy_op,signed_op,acc_op,acc_wenb,n_write,v_write,macu} = 8'b11001_01_1;
      `npuarc_MACD_OP:      {av2_inst,mpy_op,signed_op,acc_op,acc_wenb,n_write,v_write} = 7'b11111_11;
      `npuarc_MACDU_OP:     {av2_inst,mpy_op,signed_op,acc_op,acc_wenb,n_write,v_write,macu} = 8'b11011_01_1;
      //
      `npuarc_VMPY2H_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,dual_op,vector_op,acc_op,acc_wenb} = 9'b111111101;
      `npuarc_VMPY2HU_OP:   {av2_inst,mpy_op,vec_shimm,half_size,signed_op,dual_op,vector_op,acc_op,acc_wenb} = 9'b111101101;
      `npuarc_VMAC2H_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,dual_op,vector_op,acc_op,acc_wenb} = 9'b111111111;
      `npuarc_VMAC2HU_OP:   {av2_inst,mpy_op,vec_shimm,half_size,signed_op,dual_op,vector_op,acc_op,acc_wenb} = 9'b111101111;
      `npuarc_QMPYH_OP:     {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111110101_11;
      `npuarc_QMPYHU_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111100101_01;
      `npuarc_DMPYWH_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111010110_11;
      `npuarc_DMPYWHU_OP:   {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111000110_01;
      `npuarc_QMACH_OP:     {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111111101_11;
      `npuarc_QMACHU_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111101101_01;
      `npuarc_DMACWH_OP:    {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111011110_11;
      `npuarc_DMACHWHU_OP:  {av2_inst,mpy_op,vec_shimm,half_size,signed_op,acc_op,acc_wenb,dual_op,quad_op,n_write,v_write} = 11'b111001110_01;
      //
      `npuarc_VADD4H_OP:    {av2_inst,add_op,vec_shimm,half_size,quad_op,vector_op,force_cin,inv_src2} = 8'b11111100;
      `npuarc_VSUB4H_OP:    {av2_inst,add_op,vec_shimm,half_size,quad_op,vector_op,force_cin,inv_src2} = 8'b11111111;
      `npuarc_VADDSUB4H_OP: {av2_inst,add_op,vec_shimm,half_size,quad_op,vector_op,force_cin,inv_src2} = 8'b11111110;
      `npuarc_VSUBADD4H_OP: {av2_inst,add_op,vec_shimm,half_size,quad_op,vector_op,force_cin,inv_src2} = 8'b11111101;
      //
      `npuarc_VADD2_OP:     {av2_inst,add_op,dual_op,vector_op,force_cin,inv_src2} = 6'b111100;
      `npuarc_VSUB2_OP:     {av2_inst,add_op,dual_op,vector_op,force_cin,inv_src2} = 6'b111111;
      `npuarc_VADDSUB_OP:   {av2_inst,add_op,dual_op,vector_op,force_cin,inv_src2} = 6'b111110;
      `npuarc_VSUBADD_OP:   {av2_inst,add_op,dual_op,vector_op,force_cin,inv_src2} = 6'b111101;
      `npuarc_SOP_FMT: // All Single or Zero operand 32-bit insns
        begin
        case ( inst[5:0] )
        `npuarc_SWAP_OP:  begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     half_size  = 1'b1;
                     rotate_op  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_SWAPE_OP: begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     rotate_op  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_LSL16_OP: begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     half_size  = 1'b1;
                     left_shift = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_LSR16_OP: begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     half_size  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_ASR16_OP: begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     signed_op  = 1'b1;
                     half_size  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_ASR8_OP:  begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     signed_op  = 1'b1;
                     byte_size  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_LSR8_OP:  begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     byte_size  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_LSL8_OP:  begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     byte_size  = 1'b1;
                     left_shift = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_ROL8_OP:  begin
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
                   
        `npuarc_ROR8_OP:  begin
                     av2_inst = 1'b1;
                     swap_op = 1'b1;
                     fast_op = 1'b1;
                     z_write = 1'b1;
                     n_write = 1'b1;
                     byte_size  = 1'b1;
                     rotate_op  = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_NORM_OP:  begin
                     av2_inst = 1'b1;
                     norm_op   = 1'b1;
                     fast_op   = 1'b1;
                     signed_op = 1'b1;
                     z_write   = 1'b1;
                     n_write   = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_NORMW_OP: begin
                     av2_inst  = 1'b1;
                     norm_op   = 1'b1;
                     fast_op   = 1'b1;
                     signed_op = 1'b1;
                     half_size = 1'b1;
                     z_write   = 1'b1;
                     n_write   = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_FFS_OP:   begin
                     av2_inst  = 1'b1;
                     norm_op   = 1'b1;
                     fast_op   = 1'b1;
                     z_write   = 1'b1;
                     n_write   = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_FLS_OP:   begin
                     av2_inst  = 1'b1;
                     norm_op   = 1'b1;
                     fast_op   = 1'b1;
                     byte_size = 1'b1;
                     z_write   = 1'b1;
                     n_write   = 1'b1;
                     opds_in_sa = 1'b1;      // force execution in early ALU
                   end
                   
        `npuarc_ZOP_FMT: // All zero-operand 32-bit EXT0 fmts
          begin
          begin
            rf_wenb0 = 1'b0;
          end
          
          case ( {inst[14:12], inst[26:24]} )
          default: begin
                     // will be an illegal inst, unless EIA instruction matches
                     av2_inst = 1'b0;
                   end
                   
          endcase
          end
        default: begin
                   // will be an illegal inst, unless EIA instruction matches
                   av2_inst = 1'b0;
                 end
                 
        endcase
        end
      default: begin
                 // will be an illegal inst, unless EIA instruction matches
                 av2_inst = 1'b0;
               end
               
      endcase

      // enable 64-bit result write enable if 64-bit operations have
      // a defined result (i.e. result register != 62)
      //
      if ((inst[21:19] == 3'b011) || (inst[21:20] == 2'd3))
        rf_wenb0_64 = rf_wenb0;
    end


  `npuarc_GRP_USR_EXT2_32:
    begin
    // Decode the operand formats in the same way as GRP_BASECASE_32,
    // but without the exceptional formats that appear in the basecase group.
    // 64-bit source was pre-decoded and is not affected.
    // opds_in_sa/_x1 logic is decoded here more precisely.
    //
   opds_in_sa      =    eia_inst_valid & ~eia_decode_src64;
/// 
/// 
    case ( inst[23:22])
/// ================ EIA R/R START =========================
    `npuarc_REG_REG_FMT:                       // REG_REG format
      begin

        case (inst[21:16])


          `npuarc_SOP_FMT:
            case  (inst[5:0])

 // [eia-sop]: 64x64
              6'd0:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end
 // [eia-sop]: 64x64
              6'd1:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end
 // [eia-sop]: 64x64
              6'd2:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end
 // [eia-sop]: 64x64
              6'd3:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end
 // [eia-sop]: 64x64
              6'd4:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end
 // [eia-sop]: 64x64
              6'd5:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end
 // [eia-sop]: 64x64
              6'd6:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end

              `npuarc_ZOP_FMT: begin
                          rf_wenb0 = 1'b0;
                        end
                            // no explicit dest

              default:                           // SOP b,[c|limm]
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = 1'b0;
                  flag_enable = inst[15];
                  z_write = 1'b1;
                  n_write = 1'b1;
                  c_write = 1'b1;
                  v_write = 1'b1;
                end

            endcase     // SOP_FMT


          default:      // GENERIC DOP_FMT
               begin
                 rf_wa0      = inst[5:0];
                 rf_wenb0    = (rf_wa0 != 6'd62);
                 flag_enable = inst[15];
                 z_write = 1'b1;
                 n_write = 1'b1;
                 c_write = 1'b1;
                 v_write = 1'b1;
               end

       endcase          // REG_REG format, case (inst[21:16])

     end

/// ================== EIA R/R END ===========================

/// ================ EIA UIMM6 START =========================

    `npuarc_REG_U6IMM_FMT:                     // REG_U6IMM format
      begin
        sel_shimm   = 1'b1;   // default, may be overridden
        shimm       = { 26'd0, inst[11:6] };
        flag_enable = inst[15];
        z_write = 1'b1;
        n_write = 1'b1;
        c_write = 1'b1;
        v_write = 1'b1;
        
        // decode wa0 and 64-bit dest
        case (inst[21:16])


          `npuarc_SOP_FMT:
            case  (inst[5:0])

 // [eia-sop]: 64x64
              6'd0:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end
 // [eia-sop]: 64x64
              6'd1:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end
 // [eia-sop]: 64x64
              6'd2:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end
 // [eia-sop]: 64x64
              6'd3:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end
 // [eia-sop]: 64x64
              6'd4:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end
 // [eia-sop]: 64x64
              6'd5:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end
 // [eia-sop]: 64x64
              6'd6:
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = rf_wenb0;
                end

              `npuarc_ZOP_FMT: begin
                          rf_wenb0 = 1'b0;
                        end
                            // no explicit dest

              default:                           // SOP b,[c|limm]
                begin
                  rf_wa0      = { inst[14:12], inst[26:24] };
                  rf_wenb0    = (rf_wa0 != 6'd62);
                  rf_wenb0_64 = 1'b0;
                end

            endcase     // SOP_FMT


          default:      // GENERIC DOP_FMT
               begin
                 rf_wa0      = inst[5:0];
                 rf_wenb0    = (rf_wa0 != 6'd62);
                 flag_enable = inst[15];
                 z_write = 1'b1;
                 n_write = 1'b1;
                 c_write = 1'b1;
                 v_write = 1'b1;
               end

       endcase          // REG_U6 format, case (inst[21:16])

      end                                    // REG_U6IMM format

/// ================ EIA UIMM6 END =========================

    `npuarc_REG_S12IMM_FMT:                    // REG_S12IMM format
      begin
        rf_wa0      = { inst[14:12], inst[26:24] };
        rf_wenb0    = (rf_wa0 != 6'd62);
        shimm       = { {20{inst[5]}}, inst[5:0], inst[11:6] };
        sel_shimm = 1'b1; // source 2 is always short-immediate
        flag_enable = inst[15];
        z_write = 1'b1;
        n_write = 1'b1;
        c_write = 1'b1;
        v_write = 1'b1;

        case (inst[21:16])


          `npuarc_SOP_FMT:   begin
                        // raise an Illegal Instruction exception
                        illegal_instr = 1'b1;
                      end
                              // SOP_FMT disallowed
          default:    ;                        // Generic reg-s12
        endcase
      end

/// ================ EIA SIMM12 END =========================

    `npuarc_REG_COND_FMT:                      // REG_COND format
      begin
        rf_wa0      = { inst[14:12], inst[26:24] };
        rf_wenb0    = ({ inst[14:12], inst[26:24] } != 6'd62);
        q_field     = inst[4:0];
        flag_enable = inst[15];
        z_write = 1'b1;
        n_write = 1'b1;
        c_write = 1'b1;
        v_write = 1'b1;
        
        case (inst[5])
          1'b0: begin                     // EC5 requires that J or JL also sets opd3_sel
                end
                
          1'b1: begin                     // source operand only
                  shimm     = { 26'd0, inst[11:6] };
                  sel_shimm = 1'b1;
                end
                
        endcase

        case (inst[21:16])


          `npuarc_SOP_FMT:   begin
                        // raise an Illegal Instruction exception
                        illegal_instr = 1'b1;
                      end
                            // SOP_FMT disallowed

          default:                           // Generic reg-cond
              begin
                rf_wa0      = { inst[14:12], inst[26:24] };
                rf_wenb0    = ({ inst[14:12], inst[26:24] } != 6'd62);
                q_field     = inst[4:0];
                flag_enable = inst[15];
                z_write = 1'b1;
                n_write = 1'b1;
                c_write = 1'b1;
                v_write = 1'b1;
              end
        endcase
      end

/// ================ EIA REG_COND END =========================

     default:  // unsupported extension instruction 
               begin
                 // raise an Illegal Instruction exception
                 illegal_instr = 1'b1;
               end
                                      

   endcase
    end


  `npuarc_GRP_ARC_EXT0_16:
    begin
    is_16bit = 1'b1;
    if (inst[18] == 0)
      begin
      begin
      end
      
      begin
        rf_wa0   = { 1'b0, inst[20:19], inst[26:24] };
        rf_wenb0 = (rf_wa0[4:0] != 5'd30);
      end
      
      begin
        av2_inst = 1'b1;
        mov_op   = 1'b1;        // MOV src2 to dst
        fast_op  = 1'b1;        // allow next-cycle forwarding of result
      end
      
      end
    else
      begin
      begin
      end
      
      begin
        load = 1'b1;
        rf_wa1    = { 4'b0000, inst[25:24] };
        rf_wenb1  = 1'b1;
        shimm     = { 27'd0, inst[26], inst[20:19], 2'b00 };
        sel_shimm = 1'b1;
        begin
                                                              av2_inst = 1'b1;
                                                              add_op  = 1'b1;         // perform 2'c complement addition
                                                              fast_op = 1'b1;         // allow next-cycle forwarding of result
                                                            end
                                                            
      end
      
      end
    end

  `npuarc_GRP_ARC_EXT1_16:
    begin
    is_16bit = 1'b1;
    begin
    end
    
    if (inst[19] == 0)
      begin
      begin
      end
      
      if (inst[20] == 0)
        begin
          av2_inst  = 1'b1;
          load      = 1'b1;
          src2_sh2  = 1'b1;
          rf_wa1    = { 2'b00, inst[18], inst[18:16] };
          rf_wenb1  = 1'b1;
          begin
                                                              av2_inst = 1'b1;
                                                              add_op  = 1'b1;         // perform 2'c complement addition
                                                              fast_op = 1'b1;         // allow next-cycle forwarding of result
                                                            end
                                                            
        end
        
      else
        begin
        begin
          rf_wa0   = { 2'b00, inst[18], inst[18:16] };
          rf_wenb0 = 1'b1;
        end
        
        begin
          av2_inst = 1'b1;
          add_op = 1'b1;          // perform 2'c complement subtraction
          force_cin = 1'b1;       // compute A + ~B + 1
          inv_src2 = 1'b1;        // select ~B as src2
          fast_op = 1'b1;         // allow next-cycle forwarding of result
        end
        
        end
      end
    else
      begin
        av2_inst  = 1'b1;
        rf_wa0    = { 5'b00000, inst[23] };
        rf_wenb0  = 1'b1;
        shimm     = { 26'd0, inst[22:20], inst[18:16] };
        sel_shimm = 1'b1; 
        begin
                                                              av2_inst = 1'b1;
                                                              add_op  = 1'b1;         // perform 2'c complement addition
                                                              fast_op = 1'b1;         // allow next-cycle forwarding of result
                                                            end
                                                            
      end
      
    end

  `npuarc_GRP_USR_EXT0_16:
    begin
    is_16bit = 1'b1;
    if (inst[19] == 0)
      begin
      begin
        av2_inst  = 1'b1;
        rf_wa1    = 6'd1;    // load data into R1
        rf_wenb1  = ~inst[20];
        load      = ~inst[20];
        store     =  inst[20];
        shimm     = { {23{inst[26]}}, inst[26:21], inst[18:16] };
        sel_shimm = 1'b1; 
        src2_sh2  = 1'b1;
        begin
                                                              av2_inst = 1'b1;
                                                              add_op  = 1'b1;         // perform 2'c complement addition
                                                              fast_op = 1'b1;         // allow next-cycle forwarding of result
                                                            end
                                                            
      end
      
      end
    else
      begin
      begin
        av2_inst   = 1'b1;
        begin
          rf_wa1   = { 2'b00, inst[26], inst[26:24] };
          rf_wenb1 = 1'b1;
        end
        
        load       = 1'b1;
        ldi_src0   = 1'b1; // select LDI_BASE aux register as src0
        shimm      = { 25'd0, inst[23:20], inst[18:16] };
        sel_shimm  = 1'b1;
        src2_sh2   = 1'b1; // table index is always scaled by 4
      end
      
      end
    end

  `npuarc_GRP_USR_EXT1_16:
    begin
    is_16bit = 1'b1;
    if (inst[26] == 1'b0)
      begin
        av2_inst = 1'b1;
        begin
          bcc        = 1'b1;      // behaves like a bcc instruction
          rel_branch = 1'b1;      // select relative branch
          offset     = { 20'd0, inst[25:16], 2'b00 };
        end
        
        jli_src0   = 1'b1;      // select JLI_BASE aux register as src0
        link       = 1'b1;
        fast_op    = 1'b1;      // link value is available in 1 cycle
        rf_wa0     = 6'd31;     // BLINK register
        rf_wenb0   = 1'b1;      // gets written by this instruction
      end
      
    else
      begin
        av2_inst       = 1'b1;
        begin
                                                     bcc        = 1'b1;      // behaves like a bcc instruction
                                                     rel_branch = 1'b1;      // select relative branch
                                                     offset     = { 20'd0, inst[25:16], 2'b00 };
                                                   end
                                                   
        ei_op          = 1'b1;
      end
      
    end

  `npuarc_GRP_LD_ADD_RR_16:
    begin
    is_16bit = 1'b1;

    if (inst[20:19] == 2'b11)
      begin
        rf_wa0 = { 2'b00, inst[18], inst[18:16] };
        rf_wenb0 = 1'b1;
      end
        // add_s a, b, c
    else
      begin
        rf_wa1 = { 2'b00, inst[18], inst[18:16] };
        rf_wenb1 = 1'b1;
      end
       // ld_s, ldw_s, ldb_s a, [b,c]

    begin
    end
    

    case ( inst[20:19] )
    2'b00: begin
             av2_inst = 1'b1;
             load = 1'b1;
           end
           
    2'b01: begin
             av2_inst = 1'b1;
             load = 1'b1;
             byte_size = 1'b1;
           end
           
    2'b10: begin
             av2_inst = 1'b1;
             load = 1'b1;
             half_size = 1'b1;
           end
           
    2'b11: begin
             av2_inst = 1'b1;
             add_op  = 1'b1;         // perform 2'c complement addition
             fast_op = 1'b1;         // allow next-cycle forwarding of result
           end
           
    endcase
    end

  `npuarc_GRP_ADD_SUB_SH_16:
    begin
    begin
      rf_wa0 = { 2'b00, inst[23], inst[23:21] };
      rf_wenb0 = 1'b1;
      shimm  = { 29'd0, inst[18:16] };
      sel_shimm = 1'b1;
    end
    
    is_16bit = 1'b1;
    case ( inst[20:19] )
    2'b00: begin
             av2_inst = 1'b1;
             add_op  = 1'b1;         // perform 2'c complement addition
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             z_write = 1'b1;
             n_write = 1'b1;
             c_write = 1'b1;
             v_write = 1'b1;
           end
           
    2'b01: begin
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
           
    2'b10: begin
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
           
    2'b11: begin
             av2_inst = 1'b1;
             barrel_shift_op = 1'b1; // select barrel shifter
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             signed_op = 1'b1;       // arithmetic shift
             z_write = 1'b1;         // right shift by default
             n_write = 1'b1;
             c_write = 1'b1;
             opds_in_sa = 1'b1;      // force execution in early ALU
           end
           
    endcase
    end

  `npuarc_GRP_MV_CMP_ADD_16:
    begin
    is_16bit = 1'b1;
    case ( inst[20:18] )
    3'b000:  begin
      begin
        rf_wa0 = { 2'b00, inst[26], inst[26:24] };
        rf_wenb0 = 1'b1;
      end
      
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
        z_write = 1'b1;
        n_write = 1'b1;
        c_write = 1'b1;
        v_write = 1'b1;
      end
      
      end

    3'b100:  begin
      begin
      end
      
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
      
      end

    3'b001:  begin
      begin
        begin
          rf_wa0   = { 1'b0, inst[17:16], inst[23:21] };
          rf_wenb0 = (rf_wa0[4:0] != 5'd30);
        end
        
        begin
        end
        
        begin
          shimm = { {29{&inst[26:24]}}, inst[26:24]};
          sel_shimm = 1'b1;
        end
        
      end
      
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
        z_write = 1'b1;
        n_write = 1'b1;
        c_write = 1'b1;
        v_write = 1'b1;
      end
      
      end

    3'b011:  begin
      begin
        begin
          rf_wa0   = { 1'b0, inst[17:16], inst[23:21] };
          rf_wenb0 = (rf_wa0[4:0] != 5'd30);
        end
        
        begin
          shimm = { {29{&inst[26:24]}}, inst[26:24]};
          sel_shimm = 1'b1;
        end
        
      end
      
      begin
        av2_inst = 1'b1;
        mov_op   = 1'b1;        // MOV src2 to dst
        fast_op  = 1'b1;        // allow next-cycle forwarding of result
      end
      
      end

    3'b101:  begin
      begin
        begin
        end
        
        begin
          shimm = { {29{&inst[26:24]}}, inst[26:24]};
          sel_shimm = 1'b1;
        end
        
      end
      
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
      
      end

    3'b111:  begin
      begin
        rf_wa0 = { 2'b00, inst[26], inst[26:24] };
        rf_wenb0 = 1'b1;
      end
      
      begin
        av2_inst = 1'b1;
        mov_op   = 1'b1;        // MOV src2 to dst
        fast_op  = 1'b1;        // allow next-cycle forwarding of result
        q_field  = 5'b00010;    // Conditional on .ne
      end
      
      end

    default: begin
               // will be an illegal inst, unless EIA instruction matches
               av2_inst = 1'b0;
             end
             
    endcase
    end

  `npuarc_GRP_GEN_OPS_16:
    begin
    is_16bit = 1'b1;

    // First decode the operands
    case ( inst[20:16] )
    5'h00: // SOPs or ZOPS
      case ( inst[23:21] )
      3'b111:  begin
                 rf_wenb0 = 1'b0;
               end
                // ZOPs
      default: begin
               end
                // SOPS
      endcase
    5'h0b: begin
           end
                  // tst_s must not write to dest
    5'h11,
    5'h12,
    5'h13: begin
             begin
               rf_wa0   = { 2'b00, inst[26], inst[26:24] };
               rf_wenb0 = 1'b1;
             end
             
             begin
             end
             
           end
              // abs, not, neg: b <= op(c)
    5'h1e,
    5'h1f: ;                      // trap_s and brk_s have no operands
    default: begin
               begin
                 rf_wa0   = { 2'b00, inst[26], inst[26:24] };
                 rf_wenb0 = 1'b1;
               end
               
               begin
               end
               
               begin
               end
               
             end
             
    endcase

    // Second decode the operator
    case ( inst[20:16] )
    5'h00: // SOPs
      case ( inst[23:21] )
      3'b000,
      3'b001: begin
                av2_inst = 1'b1;
                jump     = 1'b1;        // select jump functionality
                dslot    = inst[21];
                opd3_sel = 1'b0;        // target is always via src1 operand
              end
                        // j_s or j_s.d
      3'b010,
      3'b011: begin
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
                       // jl_s or jl_s.d
      3'b110: begin
                av2_inst = 1'b1;
                rf_wa0       = { 2'b00, inst[26], inst[26:24] };
                rf_wenb0     = 1'b1;    // enable write to [b]
                fast_op      = 1'b1;    // allow next-cycle forwarding of result
                mov_op       = 1'b1;    // sub_s.ne b,b,b => mov.ne b,0
                
                // q_field[4] is always 0 for non-extension instructions
                //
                q_field[3:0] = 4'b0010; // NE condition
              end
                   // sub_s.ne
      3'b111: // ZOPs
        case ( inst[26:24] )
        3'b000: begin
                  av2_inst    = 1'b1;
                end
                      // nop_s
        3'b010: begin
                  av2_inst    = 1'b1;
                  flag_enable = 1'b0;  // swi does not affect the ZNCV flags
                  trap_op     = 1'b1;  // uses trap_op ucode, with byte_size == 0
                  begin
                    rf_wenb0 = 1'b0;
                  end
                  
                  opds_in_sa = 1'b1; 
                  sel_shimm  = 1'b1;   // ECR.param <= 0
                end
                      // swi_s
        3'b100: begin
                  av2_inst = 1'b1;
                  jump     = 1'b1;        // select jump functionality
                  opd3_sel = 1'b1;        // target is always via src2 operand
                
                  // q_field[4] is always 0 for non-extension instructions
                  //
                  q_field[3:0] = 4'b0001; // EQ condition
                end
                      // jeq_s [blink]
        3'b101: begin
                  av2_inst = 1'b1;
                  jump     = 1'b1;        // select jump functionality
                  opd3_sel = 1'b1;        // target is always via src2 operand
                
                  // q_field[4] is always 0 for non-extension instructions
                  //
                  q_field[3:0] = 4'b0010; // NE condition
                end
                      // jne_s [blink]
        3'b110,
        3'b111: begin
                  av2_inst = 1'b1;
                  jump     = 1'b1;        // select jump functionality
                  opd3_sel = 1'b1;        // target is always via src2 operand
                  dslot    = inst[24];
                end
                    // j_s [blink]
        default: begin
                   // raise an Illegal Instruction exception
                   illegal_instr = 1'b1;
                 end
                   // catches UNIMPL_S
        endcase
      default: begin
                 // will be an illegal inst, unless EIA instruction matches
                 av2_inst = 1'b0;
               end
               
      endcase
    5'h02: begin
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
           
    5'h04: begin
             av2_inst = 1'b1;
             and_op = 1'b1;          // perform dst = src1 & src2
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h05: begin
             av2_inst = 1'b1;
             or_op = 1'b1;           // perform logical OR
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h06: begin
             av2_inst = 1'b1;
             and_op   = 1'b1;        // perform dst = src1 & ~src2
             fast_op  = 1'b1;        // allow next-cycle forwarding of result
             inv_src2 = 1'b1;
             z_write  = 1'b1;
             n_write  = 1'b1;
           end
           
    5'h07: begin
             av2_inst = 1'b1;
             xor_op = 1'b1;          // perform logical AND
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h09: begin
             av2_inst = 1'b1;
              mpy_op     = 1'b1;
              half_size  = 1'b1;
              signed_op  = 1'b1;
              z_write    = 1'b1;
              n_write    = 1'b1;
              v_write    = 1'b1;
           end
           
    5'h0a: begin
             av2_inst = 1'b1;
              mpy_op     = 1'b1;
              half_size  = 1'b1;
              z_write    = 1'b1;
              n_write    = 1'b1;
              v_write    = 1'b1;
           end
           
    5'h0b: begin
             av2_inst = 1'b1;
             rf_wenb0 = 1'b0;        // disable destination write
             and_op = 1'b1;          // perform bit-wise AND
             z_write = 1'b1;
             n_write = 1'b1;
             flag_enable = 1'b1;     // tst and tst_s always update flags
             fast_op = 1'b1;         // flag result available after 1 cycle
           end
           
    5'h0c: begin
             av2_inst = 1'b1;
              mpy_op     = 1'b1;
              signed_op  = 1'b1;
              z_write    = 1'b1;
              n_write    = 1'b1;
              v_write    = 1'b1;
           end
           
    5'h0d: begin
             av2_inst = 1'b1;
             mov_op = 1'b1;
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             byte_size = 1'b1;
             signed_op = 1'b1;
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h0e: begin
             av2_inst = 1'b1;
             mov_op = 1'b1;
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             half_size = 1'b1;
             signed_op = 1'b1;
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h0f: begin
             av2_inst = 1'b1;
             mov_op = 1'b1;
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             byte_size = 1'b1;
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h10: begin
             av2_inst = 1'b1;
             mov_op = 1'b1;
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             half_size = 1'b1;
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h11: begin
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
           
    5'h12: begin
             av2_inst = 1'b1;
             xor_op = 1'b1;
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             inv_src1 = 1'b1;        // compute ~(0) ^ src
             z_write = 1'b1;
             n_write = 1'b1;
           end
           
    5'h13: begin
             av2_inst = 1'b1;
             add_op = 1'b1;
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             inv_src2 = 1'b1;        // compute 0 + ~src + 1
             force_cin = 1'b1;
           end
           
    5'h14: begin
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
           
    5'h15: begin
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
           
    5'h16: begin
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
           
    5'h18: begin
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
           
    5'h19: begin
             av2_inst = 1'b1;
             barrel_shift_op = 1'b1; // select barrel shifter
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             z_write = 1'b1;         // logical right shift by default
             n_write = 1'b1;
             c_write = 1'b1;
             opds_in_sa = 1'b1;      // force execution in early ALU
           end
           
    5'h1a: begin
             av2_inst = 1'b1;
             barrel_shift_op = 1'b1; // select barrel shifter
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             signed_op = 1'b1;       // arithmetic shift
             z_write = 1'b1;         // right shift by default
             n_write = 1'b1;
             c_write = 1'b1;
             opds_in_sa = 1'b1;      // force execution in early ALU
           end
           
    5'h1b: begin
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
           
    5'h1c: begin
             av2_inst = 1'b1;
             simple_shift_op = 1'b1; // select logic unit shifter
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             signed_op = 1'b1;
             z_write = 1'b1;
             n_write = 1'b1;
             c_write = 1'b1;
           end
           
    5'h1d: begin
             av2_inst = 1'b1;
             simple_shift_op = 1'b1; // select logic unit shifter
             fast_op = 1'b1;         // allow next-cycle forwarding of result
             z_write = 1'b1;
             n_write = 1'b1;
             c_write = 1'b1;
           end
           
    5'h1e: begin
             av2_inst       = 1'b1;
             flag_enable    = 1'b0;  // trap_s does not affect the ZNCV flags
             trap_op        = 1'b1;
           
             shimm          = {26'd0, inst[26:21]};
             sel_shimm      = 1'b1;
           
             byte_size      = 1'b1;  // differentiates trap_s from trap0/swi
             opds_in_sa     = 1'b1;
           end
           
    5'h1f: begin
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
             begin
               rf_wenb0 = 1'b0;
             end
             
           end
           
    default: begin
               // will be an illegal inst, unless EIA instruction matches
               av2_inst = 1'b0;
             end
             
    endcase
    end

  `npuarc_GRP_LD_WORD_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      load = 1'b1;
      begin
        rf_wa1   = { 2'b00, inst[23], inst[23:21] };
        rf_wenb1 = 1'b1;
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    src2_sh2 = 1'b1;
    end

  `npuarc_GRP_LD_BYTE_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      load = 1'b1;
      begin
        rf_wa1   = { 2'b00, inst[23], inst[23:21] };
        rf_wenb1 = 1'b1;
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    byte_size = 1'b1;
    end

  `npuarc_GRP_LD_HALF_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      load = 1'b1;
      begin
        rf_wa1   = { 2'b00, inst[23], inst[23:21] };
        rf_wenb1 = 1'b1;
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    src2_sh1 = 1'b1;
    half_size = 1'b1;
    end

  `npuarc_GRP_LD_HALFX_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      load = 1'b1;
      begin
        rf_wa1   = { 2'b00, inst[23], inst[23:21] };
        rf_wenb1 = 1'b1;
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    src2_sh1 = 1'b1;
    half_size = 1'b1;
    signed_op = 1'b1;
    end

  `npuarc_GRP_ST_WORD_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      store = 1'b1;
      opd3_sel = 1'b1;
      begin
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    src2_sh2 = 1'b1;
    end

  `npuarc_GRP_ST_BYTE_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      store = 1'b1;
      opd3_sel = 1'b1;
      begin
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    byte_size = 1'b1;
    end

  `npuarc_GRP_ST_HALF_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      store = 1'b1;
      opd3_sel = 1'b1;
      begin
      end
      
      begin
      end
      
      shimm = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    src2_sh1 = 1'b1;
    half_size = 1'b1;
    end

  `npuarc_GRP_SH_SUB_BIT_16:
    begin
    begin
      rf_wa0    = { 2'b00, inst[26], inst[26:24] };
      rf_wenb0  = 1'b1;
      shimm     = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
    end
    
    if ( inst[23:21] == 3'd7 )
      flag_enable = 1'b1;

    case ( inst[23:21] )
    3'd0: begin
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
            // asl multiple
    3'd1: begin
            av2_inst = 1'b1;
            barrel_shift_op = 1'b1; // select barrel shifter
            fast_op = 1'b1;         // allow next-cycle forwarding of result
            z_write = 1'b1;         // logical right shift by default
            n_write = 1'b1;
            c_write = 1'b1;
            opds_in_sa = 1'b1;      // force execution in early ALU
          end
            // lsr multiple
    3'd2: begin
            av2_inst = 1'b1;
            barrel_shift_op = 1'b1; // select barrel shifter
            fast_op = 1'b1;         // allow next-cycle forwarding of result
            signed_op = 1'b1;       // arithmetic shift
            z_write = 1'b1;         // right shift by default
            n_write = 1'b1;
            c_write = 1'b1;
            opds_in_sa = 1'b1;      // force execution in early ALU
          end
            // asr multiple
    3'd3: begin
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
             // subtract
    3'd4: begin
            av2_inst = 1'b1;
            or_op = 1'b1;           // perform logical OR
            bit_op = 1'b1;          // create a one-hot decoding of src2[4:0]
            src2_mask_sel = 1'b1;   // select mask in operand stage
            fast_op = 1'b1;         // allow next-cycle forwarding of result
            z_write = 1'b1;
            n_write = 1'b1;
            fast_op = 1'b1;         // flag result available after 1 cycle
          end
            // bit-set
    3'd5: begin
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
            // bit-cler
    3'd6: begin
            av2_inst = 1'b1;
            and_op = 1'b1;          // perform logical AND
            mask_op = 1'b1;         // create a mask field decoding of src2[4:0]
            src2_mask_sel = 1'b1;   // select mask in operand stage
            fast_op = 1'b1;         // allow next-cycle forwarding of result
            z_write = 1'b1;
            n_write = 1'b1;
          end
            // bit-mask
    3'd7: begin
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
          // bit-test
    endcase
    is_16bit = 1'b1;
    end

  `npuarc_GRP_SP_MEM_16:
    begin
    is_16bit = 1'b1;
    case ( inst[23:21] )
    3'd0:   begin     // ld_s  b,[sp,u7]
      begin
        av2_inst = 1'b1;
        shimm = { 27'd0, inst[20:16] };
        sel_shimm = 1'b1;
        begin
          av2_inst = 1'b1;
          add_op  = 1'b1;         // perform 2'c complement addition
          fast_op = 1'b1;         // allow next-cycle forwarding of result
        end
        
      end
      
      begin
        rf_wa1   = { 2'b00, inst[26], inst[26:24] };
        rf_wenb1 = 1'b1;
      end
      
      load     = 1'b1;
      src2_sh2 = 1'b1;
      end

    3'd1: begin     // ldb_s b,[sp,u7]
      begin
        av2_inst = 1'b1;
        shimm = { 27'd0, inst[20:16] };
        sel_shimm = 1'b1;
        begin
          av2_inst = 1'b1;
          add_op  = 1'b1;         // perform 2'c complement addition
          fast_op = 1'b1;         // allow next-cycle forwarding of result
        end
        
      end
      
      begin
        rf_wa1   = { 2'b00, inst[26], inst[26:24] };
        rf_wenb1 = 1'b1;
      end
      
      src2_sh2 = 1'b1;
      load      = 1'b1;
      byte_size = 1'b1;
      end

    3'd2: begin     // st_s  b,[sp,u7]
      begin
        av2_inst = 1'b1;
        shimm = { 27'd0, inst[20:16] };
        sel_shimm = 1'b1;
        begin
          av2_inst = 1'b1;
          add_op  = 1'b1;         // perform 2'c complement addition
          fast_op = 1'b1;         // allow next-cycle forwarding of result
        end
        
      end
      
      begin
      end
      
      store    = 1'b1;
      opd3_sel = 1'b1;
      src2_sh2 = 1'b1;
      end

    3'd3: begin     // stb_s b,[sp,u7]
      begin
        av2_inst = 1'b1;
        shimm = { 27'd0, inst[20:16] };
        sel_shimm = 1'b1;
        begin
          av2_inst = 1'b1;
          add_op  = 1'b1;         // perform 2'c complement addition
          fast_op = 1'b1;         // allow next-cycle forwarding of result
        end
        
      end
      
      begin
      end
      
      store     = 1'b1;
      opd3_sel = 1'b1;
      src2_sh2  = 1'b1;
      byte_size = 1'b1;
      end

    3'd4: begin     // add_s b,sp,u7
      rf_ra0    = 6'd28;
      rf_renb0  = 1'b1;
      shimm     = { 27'd0, inst[20:16] };
      sel_shimm = 1'b1;
      src2_sh2 = 1'b1;
      begin
        rf_wa0   = { 2'b00, inst[26], inst[26:24] };
        rf_wenb0 = 1'b1;
      end
      
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
      end

    3'd5: begin     // [add_s | sub_s] sp, sp, u7
      begin
        av2_inst = 1'b1;
        rf_wa0 = 6'd28;
        rf_wenb0 = 1'b1;
        shimm = { 27'd0, inst[20:16] };
        sel_shimm = 1'b1;
        src2_sh2 = 1'b1;
      end
      
      case ( inst[26:24] )
      3'b000: begin
                av2_inst = 1'b1;
                add_op  = 1'b1;         // perform 2'c complement addition
                fast_op = 1'b1;         // allow next-cycle forwarding of result
              end
               // add_s sp, sp, u7
      3'b001: begin
                av2_inst = 1'b1;
                add_op = 1'b1;          // perform 2'c complement subtraction
                force_cin = 1'b1;       // compute A + ~B + 1
                inv_src2 = 1'b1;        // select ~B as src2
                fast_op = 1'b1;         // allow next-cycle forwarding of result
              end
               // sub_s sp, sp, u7
      default: begin
                 // raise an Illegal Instruction exception
                 illegal_instr = 1'b1;
               end
                 // catches UNIMPL_S
      endcase
      end

    3'd6: begin
      if (inst[16] == 1'b1)
        begin
          av2_inst  = 1'b1;
          begin
          
            rf_wenb0  = 1'b1;
            rf_wa0    = 6'd28;
          end
          
          sel_shimm = 1'b1;
          shimm     = 32'd4;
          begin
                                                              av2_inst = 1'b1;
                                                              add_op  = 1'b1;         // perform 2'c complement addition
                                                              fast_op = 1'b1;         // allow next-cycle forwarding of result
                                                            end
                                                            
          pre_addr  = 1'b1;
          load = 1'b1;
          rf_wenb1  = 1'b1;
          if ( inst[20:16] == 5'd1 )
            rf_wa1  = { 2'd0, inst[26], inst[26:24] };
          else if (inst[20:16] == 5'd17)
            rf_wa1  = 6'd31;         // BLINK register
          else
            begin
              // raise an Illegal Instruction exception
              illegal_instr = 1'b1;
            end
            
        end
          // pop_s b or pop_s blink
      else
        begin
          av2_inst = 1'b1;
          begin
            // check for u[3:0] == 1111, this  is a  illegal operand
            //
            if (inst[20:17] == 4'b1111)
              begin
                // raise an Illegal Instruction exception
                illegal_instr = 1'b1;
              end
              
          end
          
          multi_op = |{ inst[26:24], inst[20:17] };
          leave_op = |{ inst[26:24], inst[20:17] };
        end
        
      end

    3'd7: begin
      if (inst[16] == 1'b1)
        begin
          av2_inst  = 1'b1;
          begin
          
            rf_wenb0  = 1'b1;
            rf_wa0    = 6'd28;
          end
          
          sel_shimm = 1'b1;
          shimm     = 32'hfffffffc;
          begin
                                                              av2_inst = 1'b1;
                                                              add_op  = 1'b1;         // perform 2'c complement addition
                                                              fast_op = 1'b1;         // allow next-cycle forwarding of result
                                                            end
                                                            
          store     = 1'b1;
          opd3_sel  = 1'b1;
          if (( inst[20:16] != 5'd1 ) && (inst[20:16] != 5'd17))
            begin
              // raise an Illegal Instruction exception
              illegal_instr = 1'b1;
            end
            
        end
         // push_s b or push_s blink
      else
        begin
          av2_inst = 1'b1;
          begin
            // check for u[3:0] == 1111, this  is a  illegal operand
            //
            if (inst[20:17] == 4'b1111)
              begin
                // raise an Illegal Instruction exception
                illegal_instr = 1'b1;
              end
              
          end
          
          multi_op = |{ inst[26:24], inst[20:17] };
          enter_op = |{ inst[26:24], inst[20:17] };
          if (inst[26] == 1'b1)   // enter_s must have bit 10 = 0
            begin
              // raise an Illegal Instruction exception
              illegal_instr = 1'b1;
            end
            
        end
        
      end
    endcase
    end

  `npuarc_GRP_GP_MEM_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      rf_wa1 = 6'd0;
      rf_wenb1 = 1'b1;
      shimm = { {24{inst[24]}}, inst[23:16] };
      sel_shimm = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    case ( inst[26:25] )
    2'd0: begin   // ld_s  r0,[gp,s11]
      load = 1'b1;
      src2_sh2 = 1'b1;
      end

    2'd1: begin   // ldb_s r0,[gp,s9]
      load = 1'b1;
      byte_size = 1'b1;
      end

    2'd2: begin   // ldw_s r0,[gp,s10]
      load = 1'b1;
      half_size = 1'b1;
      src2_sh1 = 1'b1;
      end

    2'd3: begin   // add_s r0,gp,s11
      src2_sh2 = 1'b1;
      rf_wenb0 = 1'b1;
      rf_wa0   = 6'd0;
      rf_wenb1 = 1'b0;
      fast_op  = 1'b1;
      end
    endcase
    end

  `npuarc_GRP_LD_PCL_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      load = 1'b1;
      begin
        rf_wa1   = { 2'b00, inst[26], inst[26:24] };
        rf_wenb1 = 1'b1;
      end
      
      shimm = { 24'd0, inst[23:16] };
      sel_shimm = 1'b1;
      src2_sh2 = 1'b1;
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
      end
      
    end
    
    end

  `npuarc_GRP_MV_IMM_16:
    begin
    is_16bit = 1'b1;
    begin
      av2_inst = 1'b1;
      begin
        rf_wa0   = { 2'b00, inst[26], inst[26:24] };
        rf_wenb0 = 1'b1;
      end
      
      shimm = { 24'd0, inst[23:16] };
      sel_shimm = 1'b1;
      mov_op = 1'b1;          // MOV src2 to dst
      fast_op = 1'b1;
    end
    
    end

  `npuarc_GRP_ADD_IMM_16:
    begin
    is_16bit = 1'b1;
    case ( inst[23] )
    1'b0: begin // add
      begin
        rf_wa0   = { 2'b00, inst[26], inst[26:24] };
        rf_wenb0 = 1'b1;
        begin
          shimm     = { 25'd0, inst[22:16] };
          sel_shimm = 1'b1;
        end
        
      end
      
      begin
        av2_inst = 1'b1;
        add_op  = 1'b1;         // perform 2'c complement addition
        fast_op = 1'b1;         // allow next-cycle forwarding of result
        z_write = 1'b1;
        n_write = 1'b1;
        c_write = 1'b1;
        v_write = 1'b1;
      end
      
      end
    1'b1: begin   // cmp
      begin
        shimm     = { 25'd0, inst[22:16] };
        sel_shimm = 1'b1;
      end
      
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
      
      end
    endcase
    end

  `npuarc_GRP_BRCC_S_16:
    begin
    is_16bit = 1'b1;
    begin
    end
    
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
    
    end

  `npuarc_GRP_BCC_S_16:
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
    
    

  `npuarc_GRP_BL_S_16:
    begin
    is_16bit = 1'b1;
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
    
    end
  endcase

  agu_uses_r0 = load | store;
  
  agu_uses_r1 = load & rf_renb1;
  
  src2_shifts = src2_sh1 | src2_sh2 | src2_sh3;
  
  opds_in_x1  = 1'b0
              | mpy_op
              | vector_op
              | div_op
              | eia_inst_valid & eia_decode_src64
              | uop_valid_r
              ;



  // Finalise the flag write enables by ANDing with the global
  // F-bit decoded or set by tasks such as CMP_S
  //
  begin
    z_wen = z_write & flag_enable;
    n_wen = n_write & flag_enable;
    c_wen = c_write & flag_enable;
    v_wen = v_write & flag_enable;
  end
  

  // Finalise the detection of limm data in any of the source operands.
  //
  begin
    has_limm = limm_r0 | limm_r1;
  end
  

  // Detect writes to LP_COUNT
  //
  begin
    wa0_lpc = rf_wenb0 & (rf_wa0 == 6'd60);
  end
  

  // Detect illegal operands
  //
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
  

  if (sleep_op) rf_wenb0 = 1'b0;

  // Initialize the instruction predicate to 'true'
  //
  predicate = 1'b1;
  
  // Detect whether the instruction explicitly reads and/or
  // writes to either ACCL (r58) or ACCH (r59).
  //
  reads_acc   = rf_renb0 & (rf_ra0[`npuarc_RGF_PAIR_RANGE] == `npuarc_ACC_PAIR)
              | rf_renb1 & (rf_ra1[`npuarc_RGF_PAIR_RANGE] == `npuarc_ACC_PAIR)
              ;
            
  writes_acc  = (rf_wenb0 & (rf_wa0[`npuarc_RGF_PAIR_RANGE] == `npuarc_ACC_PAIR) & (!uop_valid_r))
              | (rf_wenb1 & (rf_wa1[`npuarc_RGF_PAIR_RANGE] == `npuarc_ACC_PAIR) & (!uop_valid_r))
              ;

  may_graduate = load 
               | div_op
               ;
  // Determine whether a sign-extended LIMM is required as the store
  // data for a 64-bit STD instruction, or as the second source
  // operand for a double-precision FPU operation.
  //
  limm1_64    = limm_r1
              & (   1'b0
                  | (store  & double_size)
                )
              ;

end

  
// Assign local ARC base-case micro-code fields to micro-code vector
//
// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

assign acode[`npuarc_RF_WA0_RANGE] = rf_wa0;  // generated code
assign acode[`npuarc_RF_WENB0_RANGE] = rf_wenb0;  // generated code
assign acode[`npuarc_RF_WENB0_64_RANGE] = rf_wenb0_64;  // generated code
assign acode[`npuarc_CC_BYP_64_HAZ_RANGE] = cc_byp_64_haz;  // generated code
assign acode[`npuarc_HAS_LIMM_RANGE] = has_limm;  // generated code
assign acode[`npuarc_IS_16BIT_RANGE] = is_16bit;  // generated code
assign acode[`npuarc_SR_OP_RANGE] = sr_op;  // generated code
assign acode[`npuarc_LOOP_OP_RANGE] = loop_op;  // generated code
assign acode[`npuarc_LOCKED_RANGE] = locked;  // generated code
assign acode[`npuarc_WA0_LPC_RANGE] = wa0_lpc;  // generated code
assign acode[`npuarc_DSLOT_RANGE] = dslot;  // generated code
assign acode[`npuarc_SLEEP_OP_RANGE] = sleep_op;  // generated code
assign acode[`npuarc_ACC_WENB_RANGE] = acc_wenb;  // generated code
assign acode[`npuarc_WRITES_ACC_RANGE] = writes_acc;  // generated code
assign acode[`npuarc_LR_OP_RANGE] = lr_op;  // generated code
assign acode[`npuarc_JUMP_RANGE] = jump;  // generated code
assign acode[`npuarc_LOAD_RANGE] = load;  // generated code
assign acode[`npuarc_PREF_RANGE] = pref;  // generated code
assign acode[`npuarc_STORE_RANGE] = store;  // generated code
assign acode[`npuarc_UOP_PROL_RANGE] = uop_prol;  // generated code
assign acode[`npuarc_RF_WA1_RANGE] = rf_wa1;  // generated code
assign acode[`npuarc_RF_WENB1_RANGE] = rf_wenb1;  // generated code
assign acode[`npuarc_RF_WENB1_64_RANGE] = rf_wenb1_64;  // generated code
assign acode[`npuarc_SIGNED_OP_RANGE] = signed_op;  // generated code
assign acode[`npuarc_DOUBLE_SIZE_RANGE] = double_size;  // generated code
assign acode[`npuarc_HALF_SIZE_RANGE] = half_size;  // generated code
assign acode[`npuarc_BYTE_SIZE_RANGE] = byte_size;  // generated code
assign acode[`npuarc_RTIE_OP_RANGE] = rtie_op;  // generated code
assign acode[`npuarc_ENTER_OP_RANGE] = enter_op;  // generated code
assign acode[`npuarc_LEAVE_OP_RANGE] = leave_op;  // generated code
assign acode[`npuarc_TRAP_OP_RANGE] = trap_op;  // generated code
assign acode[`npuarc_SYNC_OP_RANGE] = sync_op;  // generated code
assign acode[`npuarc_BRK_OP_RANGE] = brk_op;  // generated code
assign acode[`npuarc_INVALID_INSTR_RANGE] = invalid_instr;  // generated code
assign acode[`npuarc_RGF_LINK_RANGE] = rgf_link;  // generated code
assign acode[`npuarc_PROD_SIGN_RANGE] = prod_sign;  // generated code
assign acode[`npuarc_MACU_RANGE] = macu;  // generated code
assign acode[`npuarc_QUAD_OP_RANGE] = quad_op;  // generated code
assign acode[`npuarc_ACC_OP_RANGE] = acc_op;  // generated code
assign acode[`npuarc_VECTOR_OP_RANGE] = vector_op;  // generated code
assign acode[`npuarc_DUAL_OP_RANGE] = dual_op;  // generated code
assign acode[`npuarc_MPY_OP_RANGE] = mpy_op;  // generated code
assign acode[`npuarc_Z_WEN_RANGE] = z_wen;  // generated code
assign acode[`npuarc_N_WEN_RANGE] = n_wen;  // generated code
assign acode[`npuarc_C_WEN_RANGE] = c_wen;  // generated code
assign acode[`npuarc_V_WEN_RANGE] = v_wen;  // generated code
assign acode[`npuarc_KERNEL_OP_RANGE] = kernel_op;  // generated code
assign acode[`npuarc_FLAG_OP_RANGE] = flag_op;  // generated code
assign acode[`npuarc_BCC_RANGE] = bcc;  // generated code
assign acode[`npuarc_LINK_RANGE] = link;  // generated code
assign acode[`npuarc_BRCC_BBIT_RANGE] = brcc_bbit;  // generated code
assign acode[`npuarc_CACHE_BYP_RANGE] = cache_byp;  // generated code
assign acode[`npuarc_SLOW_OP_RANGE] = slow_op;  // generated code
assign acode[`npuarc_FAST_OP_RANGE] = fast_op;  // generated code
assign acode[`npuarc_DIV_OP_RANGE] = div_op;  // generated code
assign acode[`npuarc_BTAB_OP_RANGE] = btab_op;  // generated code
assign acode[`npuarc_EI_OP_RANGE] = ei_op;  // generated code
assign acode[`npuarc_IN_ESLOT_RANGE] = in_eslot;  // generated code
assign acode[`npuarc_REL_BRANCH_RANGE] = rel_branch;  // generated code
assign acode[`npuarc_ILLEGAL_OPERAND_RANGE] = illegal_operand;  // generated code
assign acode[`npuarc_SWAP_OP_RANGE] = swap_op;  // generated code
assign acode[`npuarc_SETCC_OP_RANGE] = setcc_op;  // generated code
assign acode[`npuarc_CC_FIELD_RANGE] = cc_field;  // generated code
assign acode[`npuarc_Q_FIELD_RANGE] = q_field;  // generated code
assign acode[`npuarc_DEST_CR_IS_EXT_RANGE] = dest_cr_is_ext;  // generated code
assign acode[`npuarc_ADD_OP_RANGE] = add_op;  // generated code
assign acode[`npuarc_AND_OP_RANGE] = and_op;  // generated code
assign acode[`npuarc_OR_OP_RANGE] = or_op;  // generated code
assign acode[`npuarc_XOR_OP_RANGE] = xor_op;  // generated code
assign acode[`npuarc_MOV_OP_RANGE] = mov_op;  // generated code
assign acode[`npuarc_WITH_CARRY_RANGE] = with_carry;  // generated code
assign acode[`npuarc_SIMPLE_SHIFT_OP_RANGE] = simple_shift_op;  // generated code
assign acode[`npuarc_LEFT_SHIFT_RANGE] = left_shift;  // generated code
assign acode[`npuarc_ROTATE_OP_RANGE] = rotate_op;  // generated code
assign acode[`npuarc_INV_SRC1_RANGE] = inv_src1;  // generated code
assign acode[`npuarc_INV_SRC2_RANGE] = inv_src2;  // generated code
assign acode[`npuarc_BIT_OP_RANGE] = bit_op;  // generated code
assign acode[`npuarc_MASK_OP_RANGE] = mask_op;  // generated code
assign acode[`npuarc_SRC2_MASK_SEL_RANGE] = src2_mask_sel;  // generated code
assign acode[`npuarc_UOP_COMMIT_RANGE] = uop_commit;  // generated code
assign acode[`npuarc_UOP_EPIL_RANGE] = uop_epil;  // generated code
assign acode[`npuarc_UOP_EXCPN_RANGE] = uop_excpn;  // generated code
assign acode[`npuarc_PREDICATE_RANGE] = predicate;  // generated code
assign acode[`npuarc_RF_RENB0_RANGE] = rf_renb0;  // generated code
assign acode[`npuarc_RF_RENB1_RANGE] = rf_renb1;  // generated code
assign acode[`npuarc_RF_RENB0_64_RANGE] = rf_renb0_64;  // generated code
assign acode[`npuarc_RF_RENB1_64_RANGE] = rf_renb1_64;  // generated code
assign acode[`npuarc_RF_RA0_RANGE] = rf_ra0;  // generated code
assign acode[`npuarc_RF_RA1_RANGE] = rf_ra1;  // generated code
assign acode[`npuarc_JLI_SRC0_RANGE] = jli_src0;  // generated code
assign acode[`npuarc_UOP_INST_RANGE] = uop_inst;  // generated code
assign acode[`npuarc_VEC_SHIMM_RANGE] = vec_shimm;  // generated code
assign acode[`npuarc_IPROT_VIOL_RANGE] = iprot_viol;  // generated code
assign acode[`npuarc_DMB_OP_RANGE] = dmb_op;  // generated code
assign acode[`npuarc_DMB_TYPE_RANGE] = dmb_type;  // generated code
assign acode[`npuarc_FORCE_CIN_RANGE] = force_cin;  // generated code
assign acode[`npuarc_OPD3_SEL_RANGE] = opd3_sel;  // generated code
assign acode[`npuarc_MULTI_OP_RANGE] = multi_op;  // generated code
assign acode[`npuarc_ABS_OP_RANGE] = abs_op;  // generated code
assign acode[`npuarc_MIN_OP_RANGE] = min_op;  // generated code
assign acode[`npuarc_MAX_OP_RANGE] = max_op;  // generated code
assign acode[`npuarc_NORM_OP_RANGE] = norm_op;  // generated code
assign acode[`npuarc_LDI_SRC0_RANGE] = ldi_src0;  // generated code
assign acode[`npuarc_PRE_ADDR_RANGE] = pre_addr;  // generated code
assign acode[`npuarc_STIMM_OP_RANGE] = stimm_op;  // generated code
assign acode[`npuarc_SRC2_SH1_RANGE] = src2_sh1;  // generated code
assign acode[`npuarc_SRC2_SH2_RANGE] = src2_sh2;  // generated code
assign acode[`npuarc_SRC2_SH3_RANGE] = src2_sh3;  // generated code
assign acode[`npuarc_BARREL_SHIFT_OP_RANGE] = barrel_shift_op;  // generated code
assign acode[`npuarc_OPDS_IN_X1_RANGE] = opds_in_x1;  // generated code
assign acode[`npuarc_AGU_USES_R0_RANGE] = agu_uses_r0;  // generated code
assign acode[`npuarc_OPDS_IN_SA_RANGE] = opds_in_sa;  // generated code
assign acode[`npuarc_LIMM0_64_RANGE] = limm0_64;  // generated code
assign acode[`npuarc_LIMM1_64_RANGE] = limm1_64;  // generated code
assign acode[`npuarc_MAY_GRADUATE_RANGE] = may_graduate;  // generated code
assign acode[`npuarc_AGU_USES_R1_RANGE] = agu_uses_r1;  // generated code
assign acode[`npuarc_READS_ACC_RANGE] = reads_acc;  // generated code
assign acode[`npuarc_DSYNC_OP_RANGE] = dsync_op;  // generated code
assign acode[`npuarc_SRC2_SHIFTS_RANGE] = src2_shifts;  // generated code
assign acode[`npuarc_SEL_SHIMM_RANGE] = sel_shimm;  // generated code
assign acode[`npuarc_SHIMM_RANGE] = shimm;  // generated code
assign acode[`npuarc_LIMM_R0_RANGE] = limm_r0;  // generated code
assign acode[`npuarc_LIMM_R1_RANGE] = limm_r1;  // generated code
assign acode[`npuarc_OFFSET_RANGE] = offset;  // generated code


// leda NTL_CON12 on
// leda W192 on
// leda B_3400 on
// spyglass enable_block W193
// spyglass enable_block W71
endmodule
