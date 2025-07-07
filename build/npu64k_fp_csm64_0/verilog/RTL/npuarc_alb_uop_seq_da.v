// Library ARCv2HS-3.5.999999999
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
// #     #  #######  ######           #####   #######   #####
// #     #  #     #  #     #         #     #  #        #     #
// #     #  #     #  #     #         #        #        #     #
// #     #  #     #  ######           #####   #####    #     #
// #     #  #     #  #                     #  #        #   # #
// #     #  #     #  #               #     #  #        #    #
//  #####   #######  #        #####   #####   #######   #### #
//
// ===========================================================================
//
// Description:
//
// @f:uop_seq:
// @p
//  This module implements the micro-operation sequence of the ARCv2HS
//  processor. Its purpose is to emit the series of micro-instructions
//  associated with macro operations such as the reset vector, exceptions,
//  fast- and slow- interrupts, and enter/leave instructions.
// @e
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_uop_seq_da (

  ////////// Global Restart ////////////////////////////////////////////////
  //
  input                        fch_restart,         // pipeline flush

// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_WA_RCMD_RANGE]  wa_restart_cmd_r,    // pipeline restart arguments
// leda NTL_CON13C on
// leda NTL_CON37 on
  ////////// Architecturally-committed state ///////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]     ar_aux_eret_r,       // ERET aux register

  ////////// UOP-AL state input ////////////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]     al_inst,             // AL-stage data [31:0]
  input                        al_pass,             // AL-stage pass
  input                        al_uop_is_enter,     //
  input                        al_uop_do_pair,      //
  input                        al_uop_is_irtie,     //
  input                        al_uop_sirq_haz,     //
  input                        al_uop_is_ertie,     //

  ////////// AL-stage Prediction Interface /////////////////////////////////
  //
  input                        al_is_predicted,     //
  input                        al_prediction,       //
  input      [`npuarc_BR_TYPE_RANGE]  al_prediction_type,  //
  input                        al_with_dslot,       //

  ////////// Decode Stage control signals //////////////////////////////////
  //
  input                        da_kill,             // DA-stage kill
  input                        da_enable,           // DA-stage holdup/stall

  ////////// UOP-AL state input ////////////////////////////////////////////////
  //
  input      [`npuarc_UOP_BASE_RANGE] da_uop_base_r,        // UOP baseline state reg.
  input      [`npuarc_UOP_CNT_RANGE]  da_uop_spoff_r,       // SP reg. offset
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_UOP_CNT_RANGE]  da_uop_dstreg_r,      // GPR reg. index
// leda NTL_CON13C on
  input      [`npuarc_UOP_SIRQ_RANGE] da_uop_enter_r,       // UOP 'enter' state reg.
  input      [`npuarc_UOP_CNT_RANGE]  da_uop_enter_spi_r,   // 'enter' sp init. val.
  input      [`npuarc_UOP_SIRQ_RANGE] da_uop_sirq_r,        // UOP 'sirq' state reg.
  input      [`npuarc_UOP_CNT_RANGE]  da_uop_sirq_spi_r,    // 'sirq' sp init. val.
  input                        da_uop_busy_r,        // UOP is busy/active
  input                        da_uop_is_predicted_r,//
  input                        da_uop_prediction_r,  //
  input      [`npuarc_BR_TYPE_RANGE]  da_uop_prediction_type_r,//
  input      [`npuarc_BR_INFO_RANGE]  da_uop_branch_info_r, //
  input                        da_uop_with_dslot_r,  //

  output reg                   da_uop_base_cg0,      //
  output reg                   da_uop_spoff_cg0,     //
  output reg                   da_uop_dstreg_cg0,    //
  output reg                   da_uop_enter_cg0,     //
  output reg                   da_uop_enter_spi_cg0, //
  output reg                   da_uop_enter_u7_cg0,  //
  output reg                   da_uop_sirq_cg0,      //
  output reg                   da_uop_sirq_spi_cg0,  //
  output reg                   da_uop_busy_cg0,      // uop busy clock enable

  ////////// Micro-op outputs //////////////////////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]     al_uop_inst,          // micro-op instruction
  output reg [`npuarc_DATA_RANGE]     al_uop_limm,          // micro-op limm
  output reg                   al_uop_has_limm,      // micro-op has LIMM
  output reg                   al_uop_limm_r0,       // micro-op LIMM is r0
  output reg                   al_uop_limm_r1,       // micro-op LIMM is r1
  output reg [`npuarc_RGF_ADDR_RANGE] al_uop_rf_ra0,        // micro-op ra0
  output reg [`npuarc_RGF_ADDR_RANGE] al_uop_rf_ra1,        // micro-op ra1
  output reg                   al_uop_rf_renb0,      // micro-op renb0
  output reg                   al_uop_rf_renb1,      // micro-op renb1
  output reg                   al_uop_rf_renb0_64,   // micro-op renb0 (64-bit)
  output reg                   al_uop_rf_renb1_64,   // micro-op renb1 (64-bit)
  output reg                   al_uop_is_predicted,  // micro-op is pred.
  output reg                   al_uop_prediction,    // micro-op prediction
  output reg [`npuarc_BR_TYPE_RANGE]  al_uop_prediction_type, // micro-op pred. type
  output reg [`npuarc_BR_INFO_RANGE]  al_uop_branch_info,   // micro-op branch info
  output reg                   al_uop_with_dslot,    // micro-op dslot
  output reg                   da_uop_stall,         //
  output reg                   al_uop_pass,          // micro-op is valid
  output reg                   da_uop_commit,        // micro-op is terminal op
  output reg                   al_uop_prol,          // micro-op terms. PROL
  output reg                   al_uop_epil           // micro-op terms. EPIL
  );

parameter UOP_INST_AEX      =   32'h24673340;
parameter UOP_INST_J_LIMM   =   32'h20200F80;
parameter UOP_INST_MOV_SP   =   32'h24ca36c0;
parameter UOP_INST_MOV_FP   =   32'h23ca3700;
parameter UOP_INST_LD_R     =   32'h14003000;
parameter UOP_INST_ST_R     =   32'h1c003000;
parameter UOP_INST_ADD      =   32'h24803000;
parameter UOP_INST_SUB      =   32'h24823000;
parameter UOP_INST_J_SD     =   32'h7fe00000;
parameter UOP_INST_NOP      =   32'h78e00000;
parameter UOP_INST_J_C      =   32'h20200000;

// @fsm_base_emit_PROC
//
reg [`npuarc_DATA_RANGE]        base_inst;
reg [`npuarc_DATA_RANGE]        base_limm;
reg                      base_has_limm;
reg                      base_limm_r0;
reg                      base_limm_r1;
reg [`npuarc_RGF_ADDR_RANGE]    base_rf_ra0;
reg [`npuarc_RGF_ADDR_RANGE]    base_rf_ra1;
reg                      base_rf_renb0;
reg                      base_rf_renb1;
// @sirq_emit_PROC
//
reg [`npuarc_DATA_RANGE]        sirq_inst;
reg [`npuarc_DATA_RANGE]        sirq_limm;
reg [`npuarc_RNUM_RANGE]        sirq_rnum;
reg                      sirq_has_limm;
reg                      sirq_limm_r0;
reg                      sirq_limm_r1;
reg [`npuarc_RGF_ADDR_RANGE]    sirq_rf_ra0;
reg [`npuarc_RGF_ADDR_RANGE]    sirq_rf_ra1;
reg                      sirq_rf_renb0;
reg                      sirq_rf_renb1;
reg                      sirq_rf_renb0_64;
reg                      sirq_rf_renb1_64;
// @firq_emit_PROC
//





// @enter_emit_PROC
//
reg [`npuarc_DATA_RANGE]        enter_inst;
reg [`npuarc_RNUM_RANGE]        enter_rnum;
reg                      enter_has_limm;
reg                      enter_limm_r0;
reg                      enter_limm_r1;
reg [`npuarc_RGF_ADDR_RANGE]    enter_rf_ra0;
reg [`npuarc_RGF_ADDR_RANGE]    enter_rf_ra1;
reg                      enter_rf_renb0;
reg                      enter_rf_renb1;
reg                      enter_rf_renb0_64;
reg                      enter_rf_renb1_64;

// @rnum_rf_PROC:
//
reg [5:0]                rnum_rf;

// @encoding_PROC:
//
reg [`npuarc_DATA_RANGE]        a_reg_opd;
reg [`npuarc_DATA_RANGE]        s9_opd;
reg [`npuarc_DATA_RANGE]        s12_irqe_opd;
reg [`npuarc_DATA_RANGE]        s12_enter_opd;
reg [`npuarc_DATA_RANGE]        std_zz_mask;
reg [`npuarc_DATA_RANGE]        ldd_zz_mask;
reg [`npuarc_DATA_RANGE]        c_reg_opd;

// @uop_control_PROC
//
reg                      da_uop_pred;

// @limm_stall_PROC
//
reg                      limm_stall;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @fsm_base_emit_PROC:                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: fsm_base_emit_PROC

  //==========================================================================
  // Default assignments.
  //
  base_inst         = `npuarc_DATA_SIZE'd0;
  base_limm         = `npuarc_DATA_SIZE'd0;

  base_has_limm     = 1'b0;
  base_limm_r0      = 1'b0;
  base_limm_r1      = 1'b0;
  base_rf_ra0       = `npuarc_RGF_ADDR_BITS'd0;
  base_rf_ra1       = `npuarc_RGF_ADDR_BITS'd0;
  base_rf_renb0     = 1'b0;
  base_rf_renb1     = 1'b0;

  //==========================================================================
  //
  casez (da_uop_base_r)
    `npuarc_UOP_BASE_BITS'b?????_10: begin
      // emit: AEX sp, [AUX_USER_SP]
      base_inst      = (UOP_INST_AEX);
     // predecode:
      base_rf_ra0    = `npuarc_SP_REG;
      base_rf_renb0  = 1'b1;
    end
    `npuarc_UOP_BASE_BITS'b?????_11: begin
      // emit: J vector
      base_inst      = (UOP_INST_J_LIMM);
      // predecode:
      base_has_limm  = 1'b1;
      base_limm_r0   = 1'b1;


    end
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
  endcase

  //==========================================================================
  //
  casez (da_uop_base_r)
    `npuarc_UOP_BASE_BITS'b??1??_1?,
    `npuarc_UOP_BASE_BITS'b??00?_1?: begin
      base_limm_r1  = 1'b1;
      base_limm     = {   al_inst[15:0]
                        , al_inst[31:16]
                      }
                    ;
    end
    `npuarc_UOP_BASE_BITS'b??01?_1?: begin
      base_limm_r1  = 1'b1;                       
      base_limm     = ar_aux_eret_r;
    end
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
  endcase // case (da_uop_base_r)

end // block: base_emit_PROC




////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @sirq_emit_PROC:                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: sirq_emit_PROC

  //==========================================================================
  // Assign defaults.
  //
  sirq_inst          = `npuarc_DATA_SIZE'd0;
 sirq_limm           = `npuarc_DATA_SIZE'd0;

  sirq_rnum          = `npuarc_RNUM_BITS'd0;
  sirq_has_limm      = 1'b0;
  sirq_limm_r0       = 1'b0;
  sirq_limm_r1       = 1'b0;
  sirq_rf_ra0        = `npuarc_RGF_ADDR_BITS'd0;
  sirq_rf_ra1        = `npuarc_RGF_ADDR_BITS'd0;
  sirq_rf_renb0      = 1'b0;
  sirq_rf_renb1      = 1'b0;
  sirq_rf_renb0_64   = 1'b0;
  sirq_rf_renb1_64   = 1'b0;

  //==========================================================================
  // FSM state-encoding to instruction RNUM.
  //
  casez (da_uop_sirq_r)
    `npuarc_UOP_SIRQ_BITS'b????_10_0000: begin
       sirq_rnum = `npuarc_STATUS32_REG;
     end
    `npuarc_UOP_SIRQ_BITS'b????_00_1011,
    `npuarc_UOP_SIRQ_BITS'b????_10_0001: sirq_rnum = `npuarc_ILINK0_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_0010: sirq_rnum = `npuarc_BLINK_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_0100: sirq_rnum = `npuarc_LP_COUNT_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_0101: sirq_rnum = `npuarc_LP_START_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_0110: sirq_rnum = `npuarc_LP_END_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_0111: sirq_rnum = `npuarc_JLI_BASE_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_1000: sirq_rnum = `npuarc_LDI_BASE_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_1001: sirq_rnum = `npuarc_EI_BASE_REG;
    // @@ Remove regs from dstreg cnt.
    `npuarc_UOP_SIRQ_BITS'b????_11_????: sirq_rnum = da_uop_dstreg_r[`npuarc_RNUM_RANGE];

    default:                    sirq_rnum = `npuarc_RNUM_BITS'd0;
  endcase // casez (da_uop_sirq_r)

  //==========================================================================
  // FSM state-encoding to instruction word
  //
  casez (da_uop_sirq_r)
    `npuarc_UOP_SIRQ_BITS'b????_0?_1000,
    `npuarc_UOP_SIRQ_BITS'b????_0?_1001: begin
      // emit: aex sp, [AUX_USER_SP]
      sirq_inst          = (UOP_INST_AEX);
      // predecode:
      sirq_rf_ra0        = `npuarc_SP_REG;
      sirq_rf_renb0      = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??0?_1?_????: begin
      // emit: push (dstreg_r)
      sirq_inst          = (   UOP_INST_ST_R
                             | c_reg_opd
                             | s9_opd
                             | (`npuarc_DATA_SIZE'd6
                               & {`npuarc_DATA_SIZE{da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_GPR]}}
                               )
                           )
                         ;
      // predecode:
      sirq_rf_ra0        = `npuarc_SP_REG;
      sirq_rf_renb0      = 1'b1;
      sirq_rf_ra1        = sirq_rnum;
      sirq_rf_renb1      = 1'b1;
      sirq_rf_renb1_64   = da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_GPR];
    end
    `npuarc_UOP_SIRQ_BITS'b??0?_0?_1010: begin
      // emit: add sp, sp, offset
      sirq_inst          = (   UOP_INST_ADD
                             | s12_irqe_opd
                           )
                         ;

      // predecode:
      sirq_rf_ra0        = `npuarc_SP_REG;
      sirq_rf_renb0      = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??0?_00_1011: begin
      // emit: j vector
      sirq_inst          = (UOP_INST_J_LIMM);
      // predecode:
      sirq_has_limm      = 1'b1;
      sirq_limm_r0       = 1'b1;
      sirq_limm_r1       = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_1?_????: begin
      // emit: pop (dstreg_r)
      sirq_inst          = (rnum_rf != `npuarc_SP_REG)
                         ? (   UOP_INST_LD_R
                             | a_reg_opd
                             | s9_opd
                             | (`npuarc_DATA_SIZE'd384
                               & {`npuarc_DATA_SIZE{da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_GPR]}}
                               )
                           )
                         : (UOP_INST_NOP)
                         ;

      // predecode:
      sirq_rf_ra0         = `npuarc_SP_REG;
      sirq_rf_renb0       = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_0?_1010: begin
      // emit: sub sp, sp, offset
      sirq_inst          = (   UOP_INST_SUB
                             | s12_irqe_opd
                           )
                         ;
      // predecode:
      sirq_rf_ra0        = `npuarc_SP_REG;
      sirq_rf_renb0      = 1'b1;
      //sirq_rf_ra1        = `SP_REG;
      //sirq_rf_renb1      = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_00_1011: begin
      // emit: j [ilink]
      sirq_inst          = (   UOP_INST_J_C
                             | c_reg_opd
                           )
                         ;
      // predecode:
      sirq_rf_ra0        = `npuarc_ILINK0_REG;
      sirq_rf_renb0      = 1'b1;
      sirq_rf_ra1        = `npuarc_ILINK0_REG;
      sirq_rf_renb1      = 1'b1;
    end
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
  endcase // casez (da_uop_sirq_r)

  //==========================================================================
  //
  casez (da_uop_sirq_r)
    `npuarc_UOP_SIRQ_BITS'b??0?_00_1011:
      sirq_limm          = {al_inst[15:0], al_inst[31:16]};
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
      default: ;
  endcase // case (da_uop_sirq_r)
// spyglass enable_block W193
end // block: irq_emit_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @enter_emit_PROC:                                                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: enter_emit_PROC

  //==========================================================================
  // Assign defaults.
  //
  enter_inst        = `npuarc_DATA_SIZE'd0;

  enter_rnum        = `npuarc_RNUM_BITS'd0;
  enter_has_limm    = 1'b0;
  enter_limm_r0     = 1'b0;
  enter_limm_r1     = 1'b0;
  enter_rf_ra0      = `npuarc_RGF_ADDR_BITS'd0;
  enter_rf_ra1      = `npuarc_RGF_ADDR_BITS'd0;
  enter_rf_renb0    = 1'b0;
  enter_rf_renb1    = 1'b0;
  enter_rf_renb0_64 = 1'b0;
  enter_rf_renb1_64 = 1'b0;

  //==========================================================================
  // FSM state-encoding to instruction RNUM.
  //
  casez (da_uop_enter_r)
    `npuarc_UOP_SIRQ_BITS'b????_10_0010: enter_rnum = `npuarc_BLINK_REG;
    `npuarc_UOP_SIRQ_BITS'b????_10_1100: enter_rnum = `npuarc_FP_REG;
    `npuarc_UOP_SIRQ_BITS'b????_11_????: enter_rnum = da_uop_dstreg_r[`npuarc_RGF_ADDR_RANGE];
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
  endcase

  //==========================================================================
  // FSM state to encoded instruction word.
  //
  casez (da_uop_enter_r)
    `npuarc_UOP_SIRQ_BITS'b??0?_1?_????: begin
      // emit: push (r[X])
      enter_inst         = (   UOP_INST_ST_R
                             | c_reg_opd
                             | s9_opd
                             | std_zz_mask
                           )
                         ;
      // predecode:
      enter_rf_ra0       = `npuarc_SP_REG;
      enter_rf_renb0     = 1'b1;
      enter_rf_ra1       = enter_rnum;
      enter_rf_renb1     = 1'b1;
      enter_rf_renb1_64  = al_uop_do_pair;
    end
    `npuarc_UOP_SIRQ_BITS'b??0?_0?_1010: begin
      // emit: add sp, sp, offset
      enter_inst         = (   UOP_INST_ADD
                             | s12_enter_opd
                           )
                         ;

      // predecode:
      enter_rf_ra0       = `npuarc_SP_REG;
      enter_rf_renb0     = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??0?_00_1100: begin
      // emit: mov fp, sp
      enter_inst         = (UOP_INST_MOV_FP);

      // predecode:
      enter_rf_ra1       = `npuarc_SP_REG;
      enter_rf_renb1     = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_1?_????: begin
      // emit: pop (r[X])
      enter_inst         = (   UOP_INST_LD_R
                             | a_reg_opd
                             | s9_opd
                             | ldd_zz_mask
                           )
                         ;
      // predecode:
      enter_rf_ra0       = `npuarc_SP_REG;
      enter_rf_renb0     = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_0?_1010: begin
      // emit: sub sp, sp, offset
      enter_inst         = (   UOP_INST_SUB
                             | s12_enter_opd
                           )
                         ;

      // predecode:
      enter_rf_ra0       = `npuarc_SP_REG;
      enter_rf_renb0     = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_00_1100: begin
      // emit: mov sp, fp
      enter_inst         = (UOP_INST_MOV_SP);
      // predecode:
      enter_rf_ra1       = `npuarc_FP_REG;
      enter_rf_renb1     = 1'b1;
    end
    `npuarc_UOP_SIRQ_BITS'b??1?_00_1101: begin
      // emit: j.d blink
      enter_inst         = (UOP_INST_J_SD);
      // predecode:
      enter_rf_ra1       = `npuarc_BLINK_REG;
      enter_rf_renb1     = 1'b1;
    end
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
  endcase

end // block: enter_emit_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
//                                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: rnum_rf_PROC

  //==========================================================================
  // Consolidate all RNUM from the various FSM that use GPR/AUX
  // registers
  //

  rnum_rf      = `npuarc_RNUM_BITS'b0 
               | sirq_rnum
               | enter_rnum
               ;

end // block: uop_code_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @encoding_PROC:                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: encoding_PROC

  //==========================================================================
  // Special note on instruction decoding.
  //
  // During interrupt prologue/epilogue sequences, the uop sequencer
  // specifically overloads normal pipeline behaviour to denote
  // STATUS32 and XPC registers. Typically, during an ordinary
  // instruction sequences, any references to such registers would
  // result in the assertion of the invalid instruction ucode bit in
  // XA. We do not wish this to happen in this controlled case so we
  // specifically disable any ability for the instruction decode unit
  // to assert the invalid instruction bit in a uop seq. if it detects
  // a reference to an otherwise invalid register.
  //
  //==========================================================================
  // C-register operand
  //
  // The following code shifts rnum_rf into the C_RANGE field of an instr.
  // If the C_RANGE is [11:6], then rnum_rf[5:0] goes to that position
  // in the 32-bit instruction.
  
  c_reg_opd                   = `npuarc_DATA_SIZE'b0;
  c_reg_opd[`npuarc_UOP_INST_C_RANGE]= rnum_rf;


  //==========================================================================
  // A-register operand
  //
  a_reg_opd                   = `npuarc_DATA_SIZE'b0;
  a_reg_opd[`npuarc_UOP_INST_A_RANGE]= rnum_rf;

  //==========================================================================
  // s9 immediate operand (and sign extension) - [15, 23:16]
  //
  s9_opd                      = `npuarc_DATA_SIZE'b0;
  s9_opd[`npuarc_UOP_INST_S9_s_RANGE]= { da_uop_spoff_r[`npuarc_RGF_ADDR_RANGE], 2'b0 };
  s9_opd[`npuarc_UOP_INST_S9_S_RANGE]= da_uop_spoff_r[`npuarc_UOP_CNT_MSB];

  //==========================================================================
  // Slow-Interrupt: s12 immediate operand (and sign extension) -
  // [5:0, 11:16]. The s12 value is the NEGATIVE offset previously
  // calculated to derive the new stack-frame.
  //
  s12_irqe_opd                         = `npuarc_DATA_SIZE'b0;
  s12_irqe_opd[`npuarc_UOP_INST_S12_s_RANGE]  = {   da_uop_sirq_spi_r[3:0]
                                             , 2'b0
                                         }
                                         ;
  s12_irqe_opd[`npuarc_UOP_INST_S12_S_RANGE]  = {   {3{da_uop_sirq_spi_r[`npuarc_UOP_CNT_MSB]}}
                                             , da_uop_sirq_spi_r[6:4]
                                         }
                                         ;

  //==========================================================================
  // ENTER_S/LEAVE_S: s12 immediate operand (and sign extension) -
  // [5:0, 11:16]. The s12 value is the NEGATIVE offset previously
  // calculated to derive the new stack-frame.
  //
  s12_enter_opd                        = `npuarc_DATA_SIZE'b0;
  s12_enter_opd[`npuarc_UOP_INST_S12_s_RANGE] = {   da_uop_enter_spi_r[3:0]
                                             , 2'b0
                                         }
                                         ;
  s12_enter_opd[`npuarc_UOP_INST_S12_S_RANGE] = {   {3{da_uop_enter_spi_r[`npuarc_UOP_CNT_MSB]}}
                                             , da_uop_enter_spi_r[6:4]
                                         }
                                         ;

  //==========================================================================
  // ZZ-mask to permute the ST encoding into STD
  //
  std_zz_mask                          = `npuarc_DATA_SIZE'd0;
  std_zz_mask[`npuarc_UOP_INST_ST_ZZ_RANGE]   = {2{al_uop_do_pair}};

  //==========================================================================
  // ZZ-mask to premute the LD encoding into LDD
  ldd_zz_mask                          = `npuarc_DATA_SIZE'd0;
  ldd_zz_mask[`npuarc_UOP_INST_LD_ZZ_RANGE]   = {2{al_uop_do_pair}};


end // block: uop_code_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @uop_control_PROC:                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: uop_control_PROC

  //==========================================================================
  // The output of the uop_seq is valid whenever it is busy (i.e. not
  // in the IDLE state), except when there a spoff-hazard stall is
  // active.
  //
  al_uop_pass       = da_uop_busy_r
                   & (~da_uop_stall)
                    ;

  //==========================================================================
  // UOP_COMMIT is asserted to indicate the terminal instruction of
  // the sequence on the transition back to the IDLE state.
  //
  da_uop_commit     = da_uop_base_r[`npuarc_UOP_BASE_IS_TERM]
                    | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_TERM]
                    | da_uop_enter_r[`npuarc_UOP_SIRQ_IS_TERM]
                    ;

  //==========================================================================
  // UOP_PROL the current sequence was invoked by a prologue request.
  //
  al_uop_prol       = (    da_uop_base_r[`npuarc_UOP_BASE_IS_BUSY]
                        & (~da_uop_base_r[`npuarc_UOP_BASE_IS_EPIL]))
                    | (    da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_BUSY]
                        & (~da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_EPIL]))
                    ;

  //==========================================================================
  // UOP_EPIL the current sequence was invoked by an RTIE (an epilogue
  // sequence).
  //
  al_uop_epil       = da_uop_base_r[`npuarc_UOP_BASE_IS_EPIL]
                    | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_EPIL]
                    ;

  //==========================================================================
  // UOP_PRED the current instruction being emitted can accept a BPU
  // prediction if there is a valid prediction in the uop-seq state.
  //
  da_uop_pred       = da_uop_base_r[`npuarc_UOP_BASE_IS_PRED]
                    | da_uop_enter_r[`npuarc_UOP_SIRQ_IS_PRED]
                    ;
end // block: uop_control_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @uop_predecode_PROC:                                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: uop_predecode_PROC

  //==========================================================================
  // Consolidate instruction output
  //
  al_uop_inst       = base_inst
                    | enter_inst
                    | sirq_inst
                    ;
  //==========================================================================
  // Consolidate LIMM output
  //
  al_uop_limm       = base_limm
                    | sirq_limm
                    ;

  //==========================================================================
  // The micro-op sequencer will never emit a 16-bit instruction
  // therefore this output is unused.
  //
//  al_uop_is_16bit   = 1'b0
//                    ;


  //==========================================================================
  // Consolidate 'has_limm' output
  //
  al_uop_has_limm   = base_has_limm
                    | enter_has_limm
                    | sirq_has_limm
                    ;

  //==========================================================================
  // Consolidate 'limm_r0' output
  //
  al_uop_limm_r0    = base_limm_r0
                    | enter_limm_r0
                    | sirq_limm_r0
                    ;

  //==========================================================================
  // Consolidate 'limm_r1' output
  //
  al_uop_limm_r1    = base_limm_r1
                    | enter_limm_r1
                    | sirq_limm_r1
                    ;

  //==========================================================================
  // Consolidate 'rf_ra0' output
  //
  al_uop_rf_ra0     = base_rf_ra0
                    | enter_rf_ra0
                    | sirq_rf_ra0
                    ;

  //==========================================================================
  // Consolidate 'rf_ra1' output
  //
  al_uop_rf_ra1     = base_rf_ra1 
                    | enter_rf_ra1
                    | sirq_rf_ra1
                    ;

  //==========================================================================
  // Consolidate 'rf_renb0' output
  //
  al_uop_rf_renb0   = base_rf_renb0
                    | enter_rf_renb0
                    | sirq_rf_renb0
                    ;

  //==========================================================================
  // Consolidate 'rf_renb1' output
  //
  al_uop_rf_renb1   = base_rf_renb1 
                    | enter_rf_renb1
                    | sirq_rf_renb1
                    ;

  //==========================================================================
  // Consolidate 'rf_renb0_64' output
  //
  al_uop_rf_renb0_64= 1'b0
                    | enter_rf_renb0_64
                    | sirq_rf_renb0_64
                    ;

  //==========================================================================
  // Consolidate 'rf_renb1_64' output
  //
  al_uop_rf_renb1_64= 1'b0
                    | enter_rf_renb1_64
                    | sirq_rf_renb1_64
                    ;

end // block: uop_predecode_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @limm_stall_PROC                                                         //
//                                                                          //
// Process to derive the stall condition when the micro-op. sequencer       //
// attempts to emit an instruction with a LIMM, where the LIMM is           //
// supplied by the front-end, and the data has yet to reach AL.             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           emits_limm;

always @*
begin: limm_stall_PROC

  //==========================================================================
  // Identify those instructions (as a fucntion of the
  // state-variable), which emit a LIMM value from the
  // front-end. Aside from the 'enter' and reset-vector cases, those
  // states which emit LIMM are invariably the terminal instruction of
  // prologue sequences.
  //
  emits_limm        = (    da_uop_base_r[`npuarc_UOP_BASE_IS_TERM]
                        & (~da_uop_base_r[`npuarc_UOP_BASE_IS_EPIL])
                      )
                    | (    da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_TERM]
                        & (~da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_EPIL])
                      )
                    ;

  //==========================================================================
  // Stall condition derived when the sequencer emits a instruction
  // with a LIMM and the LIMM has yet to arrive from the front-end.
  //
  limm_stall        = (emits_limm & (~al_pass))
                    ;

end // block: uop_control_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @pred_PROC:                                                            //
//                                                                        //
// The initial prediction associated with the multi-op initiator          //
// instruction is retained until the instruction for which the prediction //
// applies has been emitted by the uop_seq module.                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: pred_PROC
  // leda W226 off
  // LMD: Case select expression is constant
  // LJ:  A constant select expression is required in this case
  // leda W225 off
  // LMD: Case item expression is not constant
  // LJ:  A non-constant case-itme expression is required in this case
  //
  case (1'b1)
    // Prologue sequences are identified by the fact that they emit a
    // LIMM. For such sequences, we forward any prediction associated
    // with the exception vector along with the terminating jump of
    // the sequence.
    //
    emits_limm: begin
      al_uop_is_predicted     = al_is_predicted        & da_uop_pred;
      al_uop_prediction       = al_prediction;
      al_uop_prediction_type  = al_prediction_type;
      al_uop_with_dslot       = al_with_dslot;
    end // case: emits_limm

    default: begin
      al_uop_is_predicted     = da_uop_is_predicted_r  & da_uop_pred;
      al_uop_prediction       = da_uop_prediction_r;
      al_uop_prediction_type  = da_uop_prediction_type_r;
      al_uop_with_dslot       = da_uop_with_dslot_r;
    end // case: default
  endcase
  // leda W226 on
  // leda W225 on
  al_uop_branch_info     = da_uop_branch_info_r;

end // block: pred_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @cg0_PROC                                                              //
//                                                                        //
// Centralised block where state transitions are enabled.                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                      fsm_cg0;
reg                      inst_en;
reg                      base_ini;
reg                      enter_ini;
reg                      sirq_ini;

//wire sirq_busy;
//assign sirq_busy = 1'b0;
always @*
begin: cg0_PROC

  //==========================================================================
  // Signal derived to indicate whether the instruction present in AL, if
  // successfully decoded, shall invoke a multi-op sequence in the next cycle.
  //
  inst_en                = al_pass
                         & da_enable
                         & (~da_uop_busy_r)
                         & (~da_kill)
                         ;

  //==========================================================================
  // Global/Common micro-op. sequencer stall derived as a LIMM stall
  // on prologues or an AUX_IRQ_CTRL hazard when a SIRQ operation is
  // active.
  //
  da_uop_stall           = limm_stall
//`if (`SIRQ_OPTION > 0)
//                         | (   al_uop_sirq_haz
//                             & sirq_busy
//                           )
//`endif
                         ;

  //==========================================================================
  // Global/Common fsm gate-enable on restart or when the
  // micro-op. sequencer is not stalled.
  //
  fsm_cg0                = da_kill
                         | (    da_enable
                             & (~da_uop_stall)
                           )
                         ;

  //==========================================================================
  // The 'base' FSM is initiated on the receipt of either a (1) RESET
  // or (2) an Exception restart request, or (3) on the decode of a
  // Exception epilogue initiating RTIE instruction.
  //
  //
  base_ini               = wa_restart_cmd_r[`npuarc_RSRT_IS_RESET] // (1)
                         | wa_restart_cmd_r[`npuarc_RSRT_IS_EXCPN] // (2)
                         | (al_uop_is_ertie & inst_en)      // (3)
                         ;

  da_uop_base_cg0        = fsm_cg0
                         & (   base_ini
                             | da_uop_base_r[`npuarc_UOP_BASE_IS_BUSY]
                             | fch_restart
                           )
                         ;

  //==========================================================================
  //
  enter_ini              = al_uop_is_enter
                         & inst_en
                         ;

  //==========================================================================
  // Enable 'enter' fsm state-transition on initial pass of
  // ENTER_S/LEAVE_S from AL to DA, or thereafter on 'enter'-busy.
  //
  da_uop_enter_cg0       = fsm_cg0
                         & (   enter_ini
                             | da_uop_enter_r[`npuarc_UOP_ENTER_IS_BUSY]
                             | fch_restart
                           )
                         ;

  //==========================================================================
  // Set the 'enter' stack-pointer offset initial value on the 'pass' of
  // an ENTER-class instruction from AL to DA.
  //
  da_uop_enter_spi_cg0   = enter_ini
                         ;

  //==========================================================================
  // Similarly, set the 'enter' u7 operand register on an ENTER_S/LEAVE_S.
  //
  da_uop_enter_u7_cg0    = enter_ini
                         ;

  //==========================================================================
  //
  sirq_ini               = (    wa_restart_cmd_r[`npuarc_RSRT_IS_IRQ]
                           )
                         | (   al_uop_is_irtie
                             & inst_en
                           )
                         ;

  //==========================================================================
  //
  da_uop_sirq_cg0        = fsm_cg0
                         & (   sirq_ini
                             | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_BUSY]
                             | fch_restart
                           )
                         ;

  //==========================================================================
  // The Slow-Interrupt Stack-Pointer offset pre-calculated in
  // response to an initial write to the AUX_IRQ_CTRL register
  // (infered through the 'haz' wire), it otherwise remains constant.
  //
  da_uop_sirq_spi_cg0    = al_uop_sirq_haz
                         ;

  //==========================================================================
  // Update the stack-pointer offset ('spoff') on the transition into a
  // a new multi-op sequence, or during the transition out of a memory
  // referencing state.
  //
  da_uop_spoff_cg0       = fch_restart
                         | (   da_uop_sirq_cg0
                             & (   sirq_ini
                                 | da_uop_sirq_r[`npuarc_UOP_ENTER_IS_MEM]
                               )
                           )
                         | (   da_uop_enter_cg0
                             & (   enter_ini
                                 | da_uop_enter_r[`npuarc_UOP_ENTER_IS_MEM]
                               )
                           )
                         ;

  //==========================================================================
  //
  da_uop_dstreg_cg0      = fch_restart
                         | (   da_uop_sirq_cg0
                             & (   sirq_ini
                                 | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_GPR]
                               )
                           )
                         | (   da_uop_enter_cg0
                             & (   enter_ini
                                 | da_uop_enter_r[`npuarc_UOP_ENTER_IS_GPR]
                               )
                           )
                         ;

  //==========================================================================
  // The clock-gate enable for 'uop_busy' is enabled whenever one of the
  // constituent state machines is active. The input to 'uop_busy' is set in
  // uop_seq.al as a function of the current uop_seq state.
  //
  da_uop_busy_cg0        = da_uop_base_cg0
                         | da_uop_enter_cg0
                         | da_uop_sirq_cg0
                         ;

end // block: cg0_PROC

endmodule // uop_seq_da
