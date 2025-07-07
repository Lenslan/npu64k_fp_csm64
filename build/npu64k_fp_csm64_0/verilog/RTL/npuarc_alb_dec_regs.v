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
//
// ######   #######   #####          ######   #######   #####    #####
// #     #  #        #     #         #     #  #        #     #  #     #
// #     #  #        #               #     #  #        #        #
// #     #  #####    #               ######   #####    #  ####   #####
// #     #  #        #               #   #    #        #     #        #
// #     #  #        #     #         #    #   #        #     #  #     #
// ######   #######   #####   #####  #     #  #######   #####    #####
//
// ===========================================================================
//
// Description:
//
//  The alb_dec_regs module implements the Decode stage of the Albacore
//  pipeline, which is also responsible for reading source registers.
//  This is the first stage of the Dispatch Pipe. It receives complete
//  instructions from the Issue Pipe, decodes them, and reads the source
//  register operands (replacing register values with long-immediate
//  literals where required).
//
//  This stage is also partially responsible for detecting zero-overhead
//  loop-back, and identifying instances of loop-back mis-prediction that
//  occurred in the Issue Pipe.
//
//  Branch target addresses for all control-transfer instructions are
//  computed in this stage.
//  Static predictions of branch outcomes are also computed in this stage.
//
//  The module hierarchy, at and below this module, is:
//
//        alb_reg_dec
//           |
//           +-- alb_predecode
//           |
//           +-- alb_decode
//           |
//           +-- alb_uop_seq_al
//           |
//           +-- alb_uop_seq_da
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants.
//
`include "npuarc_ucode_const.v"

// Definitions for all decode-related constants
//
`include "npuarc_decode_const.v"

// Set simulation timescale
//
`include "const.def"
`ifdef npuarc_RTL_PIPEMON  // {
`ifdef SYNTHESIS // {
`undef npuarc_RTL_PIPEMON
`endif // }
`endif // }


module npuarc_alb_dec_regs (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       rst_a,            // reset signal
  input                       in_dbl_fault_excpn_r, // In double fault

  ////////// Debug Interface /////////////////////////////////////////////////
  //
  input                       db_active,        // debug unit is active
  input                       db_valid,         //
  input   [`npuarc_DATA_RANGE]       db_inst,          //
  input   [`npuarc_DATA_RANGE]       db_limm,          //
  input   [`npuarc_PC_RANGE]         ar_pc_r,          // arch PC

  ////////// Fetch Restart interface signals /////////////////////////////////
  //
  input                       fch_restart,      // restart this stage
  input                       fch_restart_vec,  // restart for vector fetch 
  input   [`npuarc_PC_RANGE]         fch_target,       // from this PC value

  ////////// Instruction Issue handshake interface with the IFU //////////////
  //
  input                       al_pass,          // valid instruction arriving

  ////////// Instruction Issue packet from the IFU ///////////////////////////
  //
  input   [`npuarc_DATA_RANGE]       al_inst,          // the next instruction word
  input   [`npuarc_DATA_RANGE]       al_limm,          // the aligned 32-bit immediate

  //////// Exception information /////////////////////////////////////////////
  //
  input                       al_exception,     // IFU reports a fetch exception
  input   [`npuarc_FCH_EXCPN_RANGE]  al_excpn_type,    // type of exception
  input                       al_iprot_viol,    // spec ifetch viol (replay)

  //////// Branch prediction information from IFU to Execution Unit //////////
  //
  input                       al_is_predicted,  // 1 => insn is predicted
  input                       al_prediction,    // 1 => valid prediction
  input   [`npuarc_BR_TYPE_RANGE]    al_prediction_type,// type of branch prediction
  input   [`npuarc_BR_INFO_RANGE]    al_branch_info,   // br info tag
  input                       al_with_dslot,    // pred branch has dslot

  //////// Branch prediction information from UOP_SEQ to Prediction Pipe /////
  //
  output                      al_uop_snoops_pred,// 
  output                      al_uop_is_predicted,  // micro-op is pred.
  output                      al_uop_prediction,    // micro-op prediction
  output  [`npuarc_BR_TYPE_RANGE]    al_uop_prediction_type,   // micro-op pred. type
  output  [`npuarc_BR_INFO_RANGE]    al_uop_branch_info,   // micro-op branch info
  output                      al_uop_with_dslot,    // micro-op dslot
  output                      al_uop_has_limm,      // micro-op has LIMM

  //////// Branch prediction information from Prediction Pipeline ////////////
  //
  input                       da_is_eslot,      // DA insn is in an eslot  
  input                       da_is_predicted_r,// 1 => DA insn is predicted
  input                       da_prediction_r,  // branch prediction at DA
  input                       da_in_dslot_r,    // DA insn is in a dslot
  input   [`npuarc_PC_RANGE]         da_pred_bta_r,    // DA predicted br target
  input                       da_error_branch_r,// 1 => DA br error indicated
  input                       da_orphan_dslot_r,
  //
  input                       sa_is_predicted_r,// SA insn has a prediction
  input                       sa_prediction_r,  // SA predicted outcome
  input   [`npuarc_PC_RANGE]         sa_pred_bta_r,    // SA predicted br target
  input                       sa_ei_op_r,       // parent EI_S op is at SA
  input   [`npuarc_PC_RANGE]         sa_seq_pc_r,      // seq PC after SA insn

  ////////// Architecturally-committed state ////////////////////////////////
  //
  input   [`npuarc_DATA_RANGE]       ar_aux_status32_r,// (spec.) STATUS32 aux.
  input   [`npuarc_DATA_RANGE]       ar_aux_irq_ctrl_r,// (arch.) AUX_IRQ_CTRL aux.
  input                       ar_aux_irq_ctrl_upt_r, // IRQ_CTRL updt.
  input                       irq_ctrl_wen,     //to disable IRQ as is used for sp offset cal
  input   [`npuarc_DATA_RANGE]       ar_aux_eret_r,    // (arch.) AUX_ERET aux.
  input   [`npuarc_DATA_RANGE]       ar_aux_erstatus_r,// (arch.) AUX_ERSTATUS aux.
  input   [`npuarc_DATA_RANGE]       ar_aux_irq_act_r, // (arch.) AUX_IRQ_ACT aux.
  input                       int_rtie_replay_r,// force to kernal mode during epilogue
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input   [`npuarc_DATA_RANGE]       ar_aux_debug_r,   // (arch.) AUX_DEBUG aux.
  input   [`npuarc_DATA_RANGE]       ar_aux_debugi_r,  // (arch.) AUX_DEBUGI aux.
// leda NTL_CON13C on
  ////////// Machine Preemption state transition ///////////////////////////
  //

  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits used
  input   [`npuarc_DATA_RANGE]       ca_irq_act_nxt,   // Next IRQ_ACT state.
  // leda NTL_CON37 on

  ////////// Inputs from Dependency Pipeline /////////////////////////////////
  //
  input                       da_enable,        // enable input data regs
  input                       da_kill,          // kill the DA instruction

  ////////// Inputs from the Execute Pipeline ////////////////////////////////
  //
  input                       wa_restart_r,     // pipeline restart
  input   [`npuarc_WA_RCMD_RANGE]    wa_restart_cmd_r, // pipeline restart arguments


  ////////// Output the decoded fields to EIA ////////////////////////////////
  //
  output                      al_is_cond_inst,  // conditional instruction
                  
  output  [`npuarc_ISA32_GRP_RANGE]  da_group_code,    // Major group opcode
  output  [`npuarc_ISA32_DOP_RANGE]  da_dop_code_32,   // Dual-opd opcode (32-bit)
  output  [`npuarc_ISA32_SOP_RANGE]  da_sop_code_32,   // Single-opd opcode (32-bit)
  output  [`npuarc_ISA32_ZOP_RANGE]  da_zop_code_32,   // zero-opd opcode (32-bit)

  output  [`npuarc_ISA16_DOP_RANGE]  da_dop_code_16,   // Dual-opd opcode (16-bit)
  output  [`npuarc_ISA16_SOP_RANGE]  da_sop_code_16,   // Single-opd opcode (16-bit)
  output  [`npuarc_ISA16_ZOP_RANGE]  da_zop_code_16,   // zero-opd opcode (16-bit)

  output  [`npuarc_ISA32_Q_RANGE]    da_q_field,       // Instruction predicate
  output                      da_f_bit,         // F bit, enables flag updates

  ////////// Returned decoded fields from EIA ////////////////////////////////
  //
  input                       eia_inst_valid,   // 1=> EIA inst was decoded
  input                       eia_decode_src64, // eia inst has 64-bit source opds
  input                       eia_illegal_cond, // Illegal extension condition
  input                       eia_kernel,       // kernel priv needed
  input                       eia_illegal_cr_access,  // ro/wo violations

  input                       eia_ra0_is_ext,   // rf_ra0 is EIA core register
  input                       eia_ra1_is_ext,   // rf_ra1 is EIA core register
  input                       eia_wa0_is_ext,   // rf_wa0 is EIA core register
  input                       eia_wa1_is_ext,   // rf_wa1 is EIA core register
  input                       eia_multi_cycle,  // ++ Eia inst is multi-cycle
  input                       eia_flag_wen,     // Execute inst defines flags
  input                       eia_dst_wen,      // Execute inst writes to explicit reg

  ////////// hazard cycles when stack pointer offset is being calculated /////
  //It takes 3 cycles
  // 
  output                      al_uop_sirq_haz,    //

  ////////// Interface with the Operand stage ////////////////////////////////
  //
  output     [`npuarc_PC_RANGE]      sa_pc_nxt,        // PC of decoded instruction
  output     [`npuarc_DATA_RANGE]    sa_limm_nxt,      // next LIMM for SA stage
  output reg [`npuarc_SA_CODE_WIDTH-1:0] sa_code_nxt,  // decoded control vector
  output reg [`npuarc_PC_RANGE]      sa_seq_pc_nxt,    // next sequential PC
  output                      sa_is_16bit_nxt,  //
  output reg                  da_iprot_viol_r,  // spec ifetch prot viol
                     

`ifdef npuarc_RTL_PIPEMON // {
  output reg [31:0]     Pda_limm_r,
  output reg       Pda_is_16bit_r,
  output reg       Pda_has_limm_r,
  output reg [31:0]     Pda_inst_r,
`endif // }

  ////////// Interface with the Dependency and Control Pipeline //////////////
  //
  input                       da_pass,          // passing a valid instruction

  output                      al_uop_pass,      //
  output                      da_dslot,         // DA inst has dslot
  output                      al_uop_epil,      // uop epil SM is active
  output                      da_ei_op,         // DA insn is an EI_S
  output                      da_ldi_src0,      // LDI insn at DA
  output                      da_jli_src0,      // LDI insn at DA
  output                      da_uop_u7_pcl,    // LEAVE_S u7 pcl bit
  output    [`npuarc_ZNCV_RANGE]     da_zncv_wen,      //
  output                      da_uop_stall,     // uop-seq reqs. stall
  output                      da_rtie_op_r,     // da rtie op
  output reg                  da_uop_prol_r,    // DA insn is in prologue
  output reg                  da_uop_busy_r,    // uop-seq is active
  output reg                  da_uop_is_excpn_r,// 'da' ins is for excpn (uop)
  output reg                  da_uop_is_sirq_r, // ''da' ins is for sirq (uop)
//  output reg                  da_uop_is_gpr_r,  // ''da' ins is for gpr (uop)
  output reg                  da_valid_r,       // DA-stage validity
  output reg[`npuarc_RGF_ADDR_RANGE] da_rf_ra0_r,      // next read port 0 address
  output reg[`npuarc_RGF_ADDR_RANGE] da_rf_ra1_r,      // next read port 1 address
  output  [`npuarc_RGF_ADDR_RANGE]   da_rf_wa0,        // next read port 0 address
  output  [`npuarc_RGF_ADDR_RANGE]   da_rf_wa1,        // next read port 1 address
  output                      da_rf_wenb0,      // next read port 0 enable
  output                      da_rf_wenb1,      // next read port 1 enable
  output                      da_rf_wenb0_64,   // dest reg0 is 64-bit reg-pair
  output                      da_rf_wenb1_64,   // dest reg1 is 64-bit reg-pair
  output reg                  da_rf_renb0_64_r, // reg0 is 64-bit reg-pair
  output reg                  da_rf_renb0_r,    // next read port 0 enable
  output reg                  da_rf_renb1_64_r, // reg1 is 64-bit reg-pair
  output reg                  da_rf_renb1_r     // next read port 1 enable
);

parameter BR_TAKEN   = 1'b1;

//////////////////////////////////////////////////////////////////////////////
// Registers, register next value signals, and register update signals      //
//////////////////////////////////////////////////////////////////////////////

wire  [`npuarc_DATA_RANGE]         predecode_inst;     // Insn. used by predecoder

// @da_debugi_PROC:
//
reg                         permute_j_to_brk;   // Convert J into BRK

reg   [`npuarc_PC_RANGE]           da_pc_r;            // Decode-stage PC
reg   [`npuarc_DATA_RANGE]         da_inst_r /* verilator public_flat */;          // current DA instruction
reg   [`npuarc_DATA_RANGE]         da_limm_r /* verilator public_flat */;          // Long-immediate data
reg                         da_limm_r0_r;       // Next read port 0 limm-select
reg                         da_limm_r1_r;       // Next read port 1 limm-select
reg                         da_has_limm_r /* verilator public_flat */;      // Any read reg is limm
reg                         da_is_16bit_r /* verilator public_flat */;      // Insn uses 16-bit format
reg                         da_uop_commit_r;    // Insn terminates uop
reg                         da_uop_epil_r;      // Insn terminates EPIL


// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg     [`npuarc_FCH_EXCPN_RANGE]  da_excpn_type_r;    // exception type at DA
// leda NTL_CON32 on

reg [`npuarc_UOP_CNT_RANGE]        da_uop_spoff_r;     // stack-pointer offset (uop)
reg [`npuarc_UOP_CNT_RANGE]        da_uop_dstreg_r;    // dest. reg. pointer (uop)
reg [`npuarc_UOP_ENTER_RANGE]      da_uop_enter_r;     // 'enter' state variable (uop)
reg [`npuarc_UOP_CNT_RANGE]        da_uop_enter_spi_r; // 'enter' sp ini. value (uop)
reg [6:0]                   da_uop_enter_u7_r;  // 'enter' u7 oprnd (uop)
reg [`npuarc_UOP_SIRQ_RANGE]       da_uop_sirq_r;      // 'sirq' state variable (uop)
reg [`npuarc_UOP_CNT_RANGE]        da_uop_sirq_spi_r;  // 'sirq' sp ini. value (uop)
reg [`npuarc_UOP_BASE_RANGE]       da_uop_base_r;      // 'base' state variable (uop)
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  used in submodule
reg                         da_uop_pkilled_r;   // prol killed by exception during active da_uop_base_r 
// leda NTL_CON32 on
reg                         da_uop_is_predicted_r;//
reg                         da_uop_prediction_r;  //
reg [`npuarc_BR_TYPE_RANGE]        da_uop_prediction_type_r;//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_BR_INFO_RANGE]        da_uop_branch_info_r;
// leda NTL_CON32 on
reg                         da_uop_with_dslot_r;//


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Wires and regs for local non-registered signals                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Micro-code word produced by instruction decoder at this pipeline stage
//
wire  [`npuarc_DA_CODE_WIDTH-1:0]  da_code;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  potential used ucode generated wires
// Assign each microcode field to a named wire or wire-vector
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

assign da_rf_wa0    = da_code[`npuarc_RF_WA0_RANGE];  // generated code
assign da_rf_wenb0  = da_code[`npuarc_RF_WENB0_RANGE];  // generated code
assign da_rf_wenb0_64  = da_code[`npuarc_RF_WENB0_64_RANGE];  // generated code
wire   da_cc_byp_64_haz;  // generated code
assign da_cc_byp_64_haz  = da_code[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
wire   da_has_limm;  // generated code
assign da_has_limm  = da_code[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   da_is_16bit;  // generated code
assign da_is_16bit  = da_code[`npuarc_IS_16BIT_RANGE];  // generated code
wire   da_sr_op;  // generated code
assign da_sr_op  = da_code[`npuarc_SR_OP_RANGE];  // generated code
wire   da_loop_op;  // generated code
assign da_loop_op  = da_code[`npuarc_LOOP_OP_RANGE];  // generated code
wire   da_locked;  // generated code
assign da_locked  = da_code[`npuarc_LOCKED_RANGE];  // generated code
wire   da_wa0_lpc;  // generated code
assign da_wa0_lpc  = da_code[`npuarc_WA0_LPC_RANGE];  // generated code
assign da_dslot     = da_code[`npuarc_DSLOT_RANGE];  // generated code
wire   da_sleep_op;  // generated code
assign da_sleep_op  = da_code[`npuarc_SLEEP_OP_RANGE];  // generated code
wire   da_acc_wenb;  // generated code
assign da_acc_wenb  = da_code[`npuarc_ACC_WENB_RANGE];  // generated code
wire   da_writes_acc;  // generated code
assign da_writes_acc  = da_code[`npuarc_WRITES_ACC_RANGE];  // generated code
wire   da_lr_op;  // generated code
assign da_lr_op  = da_code[`npuarc_LR_OP_RANGE];  // generated code
wire   da_jump;  // generated code
assign da_jump  = da_code[`npuarc_JUMP_RANGE];  // generated code
wire   da_load;  // generated code
assign da_load  = da_code[`npuarc_LOAD_RANGE];  // generated code
wire   da_pref;  // generated code
assign da_pref  = da_code[`npuarc_PREF_RANGE];  // generated code
wire   da_store;  // generated code
assign da_store  = da_code[`npuarc_STORE_RANGE];  // generated code
wire   da_uop_prol;  // generated code
assign da_uop_prol  = da_code[`npuarc_UOP_PROL_RANGE];  // generated code
assign da_rf_wa1    = da_code[`npuarc_RF_WA1_RANGE];  // generated code
assign da_rf_wenb1  = da_code[`npuarc_RF_WENB1_RANGE];  // generated code
assign da_rf_wenb1_64  = da_code[`npuarc_RF_WENB1_64_RANGE];  // generated code
wire   da_signed_op;  // generated code
assign da_signed_op  = da_code[`npuarc_SIGNED_OP_RANGE];  // generated code
wire   da_double_size;  // generated code
assign da_double_size  = da_code[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
wire   da_half_size;  // generated code
assign da_half_size  = da_code[`npuarc_HALF_SIZE_RANGE];  // generated code
wire   da_byte_size;  // generated code
assign da_byte_size  = da_code[`npuarc_BYTE_SIZE_RANGE];  // generated code
wire   da_rtie_op;  // generated code
assign da_rtie_op  = da_code[`npuarc_RTIE_OP_RANGE];  // generated code
wire   da_enter_op;  // generated code
assign da_enter_op  = da_code[`npuarc_ENTER_OP_RANGE];  // generated code
wire   da_leave_op;  // generated code
assign da_leave_op  = da_code[`npuarc_LEAVE_OP_RANGE];  // generated code
wire   da_trap_op;  // generated code
assign da_trap_op  = da_code[`npuarc_TRAP_OP_RANGE];  // generated code
wire   da_sync_op;  // generated code
assign da_sync_op  = da_code[`npuarc_SYNC_OP_RANGE];  // generated code
wire   da_brk_op;  // generated code
assign da_brk_op  = da_code[`npuarc_BRK_OP_RANGE];  // generated code
wire   da_invalid_instr;  // generated code
assign da_invalid_instr  = da_code[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   da_rgf_link;  // generated code
assign da_rgf_link  = da_code[`npuarc_RGF_LINK_RANGE];  // generated code
wire   da_prod_sign;  // generated code
assign da_prod_sign  = da_code[`npuarc_PROD_SIGN_RANGE];  // generated code
wire   da_macu;  // generated code
assign da_macu  = da_code[`npuarc_MACU_RANGE];  // generated code
wire   da_quad_op;  // generated code
assign da_quad_op  = da_code[`npuarc_QUAD_OP_RANGE];  // generated code
wire   da_acc_op;  // generated code
assign da_acc_op  = da_code[`npuarc_ACC_OP_RANGE];  // generated code
wire   da_vector_op;  // generated code
assign da_vector_op  = da_code[`npuarc_VECTOR_OP_RANGE];  // generated code
wire   da_dual_op;  // generated code
assign da_dual_op  = da_code[`npuarc_DUAL_OP_RANGE];  // generated code
assign da_mpy_op    = da_code[`npuarc_MPY_OP_RANGE];  // generated code
wire   da_z_wen;  // generated code
assign da_z_wen  = da_code[`npuarc_Z_WEN_RANGE];  // generated code
wire   da_n_wen;  // generated code
assign da_n_wen  = da_code[`npuarc_N_WEN_RANGE];  // generated code
wire   da_c_wen;  // generated code
assign da_c_wen  = da_code[`npuarc_C_WEN_RANGE];  // generated code
wire   da_v_wen;  // generated code
assign da_v_wen  = da_code[`npuarc_V_WEN_RANGE];  // generated code
wire   da_kernel_op;  // generated code
assign da_kernel_op  = da_code[`npuarc_KERNEL_OP_RANGE];  // generated code
wire   da_flag_op;  // generated code
assign da_flag_op  = da_code[`npuarc_FLAG_OP_RANGE];  // generated code
wire   da_bcc;  // generated code
assign da_bcc  = da_code[`npuarc_BCC_RANGE];  // generated code
wire   da_link;  // generated code
assign da_link  = da_code[`npuarc_LINK_RANGE];  // generated code
wire   da_brcc_bbit;  // generated code
assign da_brcc_bbit  = da_code[`npuarc_BRCC_BBIT_RANGE];  // generated code
wire   da_cache_byp;  // generated code
assign da_cache_byp  = da_code[`npuarc_CACHE_BYP_RANGE];  // generated code
wire   da_slow_op;  // generated code
assign da_slow_op  = da_code[`npuarc_SLOW_OP_RANGE];  // generated code
wire   da_fast_op;  // generated code
assign da_fast_op  = da_code[`npuarc_FAST_OP_RANGE];  // generated code
wire   da_div_op;  // generated code
assign da_div_op  = da_code[`npuarc_DIV_OP_RANGE];  // generated code
wire   da_btab_op;  // generated code
assign da_btab_op  = da_code[`npuarc_BTAB_OP_RANGE];  // generated code
assign da_ei_op     = da_code[`npuarc_EI_OP_RANGE];  // generated code
wire   da_in_eslot;  // generated code
assign da_in_eslot  = da_code[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   da_rel_branch;  // generated code
assign da_rel_branch  = da_code[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   da_illegal_operand;  // generated code
assign da_illegal_operand  = da_code[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   da_swap_op;  // generated code
assign da_swap_op  = da_code[`npuarc_SWAP_OP_RANGE];  // generated code
wire   da_setcc_op;  // generated code
assign da_setcc_op  = da_code[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  da_cc_field;  // generated code
assign da_cc_field  = da_code[`npuarc_CC_FIELD_RANGE];  // generated code
assign da_q_field   = da_code[`npuarc_Q_FIELD_RANGE];  // generated code
assign da_dest_cr_is_ext  = da_code[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   da_add_op;  // generated code
assign da_add_op  = da_code[`npuarc_ADD_OP_RANGE];  // generated code
wire   da_and_op;  // generated code
assign da_and_op  = da_code[`npuarc_AND_OP_RANGE];  // generated code
wire   da_or_op;  // generated code
assign da_or_op  = da_code[`npuarc_OR_OP_RANGE];  // generated code
wire   da_xor_op;  // generated code
assign da_xor_op  = da_code[`npuarc_XOR_OP_RANGE];  // generated code
wire   da_mov_op;  // generated code
assign da_mov_op  = da_code[`npuarc_MOV_OP_RANGE];  // generated code
wire   da_with_carry;  // generated code
assign da_with_carry  = da_code[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   da_simple_shift_op;  // generated code
assign da_simple_shift_op  = da_code[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   da_left_shift;  // generated code
assign da_left_shift  = da_code[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   da_rotate_op;  // generated code
assign da_rotate_op  = da_code[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   da_inv_src1;  // generated code
assign da_inv_src1  = da_code[`npuarc_INV_SRC1_RANGE];  // generated code
wire   da_inv_src2;  // generated code
assign da_inv_src2  = da_code[`npuarc_INV_SRC2_RANGE];  // generated code
wire   da_bit_op;  // generated code
assign da_bit_op  = da_code[`npuarc_BIT_OP_RANGE];  // generated code
wire   da_mask_op;  // generated code
assign da_mask_op  = da_code[`npuarc_MASK_OP_RANGE];  // generated code
wire   da_src2_mask_sel;  // generated code
assign da_src2_mask_sel  = da_code[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
wire   da_uop_commit;  // generated code
assign da_uop_commit  = da_code[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   da_uop_epil;  // generated code
assign da_uop_epil  = da_code[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   da_uop_excpn;  // generated code
assign da_uop_excpn  = da_code[`npuarc_UOP_EXCPN_RANGE];  // generated code
wire   da_predicate;  // generated code
assign da_predicate  = da_code[`npuarc_PREDICATE_RANGE];  // generated code
wire   da_rf_renb0;  // generated code
assign da_rf_renb0  = da_code[`npuarc_RF_RENB0_RANGE];  // generated code
wire   da_rf_renb1;  // generated code
assign da_rf_renb1  = da_code[`npuarc_RF_RENB1_RANGE];  // generated code
wire   da_rf_renb0_64;  // generated code
assign da_rf_renb0_64  = da_code[`npuarc_RF_RENB0_64_RANGE];  // generated code
wire   da_rf_renb1_64;  // generated code
assign da_rf_renb1_64  = da_code[`npuarc_RF_RENB1_64_RANGE];  // generated code
wire [5:0]  da_rf_ra0;  // generated code
assign da_rf_ra0  = da_code[`npuarc_RF_RA0_RANGE];  // generated code
wire [5:0]  da_rf_ra1;  // generated code
assign da_rf_ra1  = da_code[`npuarc_RF_RA1_RANGE];  // generated code
assign da_jli_src0  = da_code[`npuarc_JLI_SRC0_RANGE];  // generated code
wire   da_uop_inst;  // generated code
assign da_uop_inst  = da_code[`npuarc_UOP_INST_RANGE];  // generated code
wire   da_vec_shimm;  // generated code
assign da_vec_shimm  = da_code[`npuarc_VEC_SHIMM_RANGE];  // generated code
wire   da_iprot_viol;  // generated code
assign da_iprot_viol  = da_code[`npuarc_IPROT_VIOL_RANGE];  // generated code
wire   da_dmb_op;  // generated code
assign da_dmb_op  = da_code[`npuarc_DMB_OP_RANGE];  // generated code
wire [2:0]  da_dmb_type;  // generated code
assign da_dmb_type  = da_code[`npuarc_DMB_TYPE_RANGE];  // generated code
wire   da_force_cin;  // generated code
assign da_force_cin  = da_code[`npuarc_FORCE_CIN_RANGE];  // generated code
wire   da_opd3_sel;  // generated code
assign da_opd3_sel  = da_code[`npuarc_OPD3_SEL_RANGE];  // generated code
wire   da_multi_op;  // generated code
assign da_multi_op  = da_code[`npuarc_MULTI_OP_RANGE];  // generated code
wire   da_abs_op;  // generated code
assign da_abs_op  = da_code[`npuarc_ABS_OP_RANGE];  // generated code
wire   da_min_op;  // generated code
assign da_min_op  = da_code[`npuarc_MIN_OP_RANGE];  // generated code
wire   da_max_op;  // generated code
assign da_max_op  = da_code[`npuarc_MAX_OP_RANGE];  // generated code
wire   da_norm_op;  // generated code
assign da_norm_op  = da_code[`npuarc_NORM_OP_RANGE];  // generated code
assign da_ldi_src0  = da_code[`npuarc_LDI_SRC0_RANGE];  // generated code
wire   da_pre_addr;  // generated code
assign da_pre_addr  = da_code[`npuarc_PRE_ADDR_RANGE];  // generated code
wire   da_stimm_op;  // generated code
assign da_stimm_op  = da_code[`npuarc_STIMM_OP_RANGE];  // generated code
wire   da_src2_sh1;  // generated code
assign da_src2_sh1  = da_code[`npuarc_SRC2_SH1_RANGE];  // generated code
wire   da_src2_sh2;  // generated code
assign da_src2_sh2  = da_code[`npuarc_SRC2_SH2_RANGE];  // generated code
wire   da_src2_sh3;  // generated code
assign da_src2_sh3  = da_code[`npuarc_SRC2_SH3_RANGE];  // generated code
wire   da_barrel_shift_op;  // generated code
assign da_barrel_shift_op  = da_code[`npuarc_BARREL_SHIFT_OP_RANGE];  // generated code
wire   da_opds_in_x1;  // generated code
assign da_opds_in_x1  = da_code[`npuarc_OPDS_IN_X1_RANGE];  // generated code
wire   da_agu_uses_r0;  // generated code
assign da_agu_uses_r0  = da_code[`npuarc_AGU_USES_R0_RANGE];  // generated code
wire   da_opds_in_sa;  // generated code
assign da_opds_in_sa  = da_code[`npuarc_OPDS_IN_SA_RANGE];  // generated code
wire   da_limm0_64;  // generated code
assign da_limm0_64  = da_code[`npuarc_LIMM0_64_RANGE];  // generated code
wire   da_limm1_64;  // generated code
assign da_limm1_64  = da_code[`npuarc_LIMM1_64_RANGE];  // generated code
assign da_may_graduate  = da_code[`npuarc_MAY_GRADUATE_RANGE];  // generated code
wire   da_agu_uses_r1;  // generated code
assign da_agu_uses_r1  = da_code[`npuarc_AGU_USES_R1_RANGE];  // generated code
wire   da_reads_acc;  // generated code
assign da_reads_acc  = da_code[`npuarc_READS_ACC_RANGE];  // generated code
wire   da_dsync_op;  // generated code
assign da_dsync_op  = da_code[`npuarc_DSYNC_OP_RANGE];  // generated code
wire   da_src2_shifts;  // generated code
assign da_src2_shifts  = da_code[`npuarc_SRC2_SHIFTS_RANGE];  // generated code
wire   da_sel_shimm;  // generated code
assign da_sel_shimm  = da_code[`npuarc_SEL_SHIMM_RANGE];  // generated code
wire [31:0]  da_shimm;  // generated code
assign da_shimm  = da_code[`npuarc_SHIMM_RANGE];  // generated code
wire   da_limm_r0;  // generated code
assign da_limm_r0  = da_code[`npuarc_LIMM_R0_RANGE];  // generated code
wire   da_limm_r1;  // generated code
assign da_limm_r1  = da_code[`npuarc_LIMM_R1_RANGE];  // generated code
wire [31:0]  da_offset;  // generated code
assign da_offset  = da_code[`npuarc_OFFSET_RANGE];  // generated code

// leda NTL_CON13A on

reg                         da_valid_nxt;       // next DA cycle validity
reg   [`npuarc_PC_RANGE]           da_pc_nxt;          // next DA PC

reg   [`npuarc_DATA_RANGE]         da_inst_nxt;        // next DA instruction
reg   [`npuarc_DATA_RANGE]         da_limm_nxt;        // next DA limm
reg   [`npuarc_RGF_ADDR_RANGE]     da_rf_ra0_nxt;      // next read port 0 address
reg   [`npuarc_RGF_ADDR_RANGE]     da_rf_ra1_nxt;      // next read port 1 address
reg                         da_rf_renb0_nxt;    // next read port 0 enb signal
reg                         da_rf_renb1_nxt;    // next read port 1 enb signal
reg                         da_limm_r0_nxt;     // next read port 0 limm-select
reg                         da_limm_r1_nxt;     // next read port 1 limm-select
reg                         da_has_limm_nxt;    // next insn has_limm signal
reg                         da_is_16bit_nxt;    // next insn is_16bit signal
reg                         da_rf_renb0_64_nxt; // next reg0 is 64-bit reg-pair
reg                         da_rf_renb1_64_nxt; // next reg1 is 64-bit reg-pair
reg                         da_is_vec_instr;
reg                         da_uop_commit_nxt;  // next insn terminates uop.
reg                         da_uop_prol_nxt;    //
reg                         da_uop_epil_nxt;    //
reg                         da_valid_cg0;       // reg enable for DA valid
reg                         da_issue_cg0;       // reg enable for issue to DA
reg                         da_excpn_cg0;       // reg enable for excpn info
reg                         da_uop_valid_r;      //

// Wires for AL-stage predecoded instruction outputs
//
wire  [`npuarc_RGF_ADDR_RANGE]     al_rf_ra0;          // AL read port 0 address
wire  [`npuarc_RGF_ADDR_RANGE]     al_rf_ra1;          // AL read port 1 address
wire                        al_rf_renb0;        // AL read port 0 enb signal
wire                        al_rf_renb1;        // AL read port 1 enb signal
wire                        al_limm_r0;         // AL read port 0 limm-select
wire                        al_limm_r1;         // AL read port 1 limm-select
wire                        al_has_limm;        // AL insn has_limm signal
wire                        al_is_16bit;        // AL insn is_16bit signal
wire                        al_rf_renb0_64;     // AL reg0 is 64-bit reg-pair
wire                        al_rf_renb1_64;     // AL reg1 is 64-bit reg-pair

// Wires for AL-stage uop sequencer outputs
//
wire                        al_uop_is_enter;    //
wire                        al_uop_do_pair;     //
wire                        al_uop_is_irtie;    // AL is Intrupt. RTIE
wire                        al_uop_is_ertie;    // AL is Excpn RTIE
wire  [`npuarc_UOP_CNT_RANGE]      da_uop_spoff_nxt;   // SP offset next value
wire  [`npuarc_UOP_CNT_RANGE]      da_uop_dstreg_nxt;  // Dst.reg. next value
wire  [`npuarc_UOP_ENTER_RANGE]    da_uop_enter_nxt;   // 'enter' fsm next state
wire  [`npuarc_UOP_CNT_RANGE]      da_uop_enter_spi_nxt;//'enter' sp initial value
wire  [6:0]                 da_uop_enter_u7_nxt;// 'enter' u7 operand
wire  [`npuarc_UOP_SIRQ_RANGE]     da_uop_sirq_nxt;    // 'sirq' fsm next state
wire  [`npuarc_UOP_CNT_RANGE]      da_uop_sirq_spi_nxt;// 'sirq' sp initial value
wire  [`npuarc_UOP_BASE_RANGE]     da_uop_base_nxt;    // 'base' fsm next state
wire                        da_uop_busy_nxt;    // uop_seq busy next state
wire                        da_uop_pred_cg0;    // uop_seq pred. state
wire                        da_uop_pkilled_nxt;
// Wires for DA-stage uop sequencer outputs
//
wire  [`npuarc_DATA_RANGE]         al_uop_inst;        // next issued UOP instruction
wire  [`npuarc_DATA_RANGE]         al_uop_limm;        // next issued UOP limm
wire  [`npuarc_RGF_ADDR_RANGE]     al_uop_rf_ra0;      // UOP read port 0 address
wire  [`npuarc_RGF_ADDR_RANGE]     al_uop_rf_ra1;      // UOP read port 1 address
wire                        al_uop_rf_renb0;    // UOP read port 0 enb signal
wire                        al_uop_rf_renb1;    // UOP read port 1 enb signal
wire                        al_uop_limm_r0;     // UOP read port 0 limm-select
wire                        al_uop_limm_r1;     // UOP read port 1 limm-select
//wire                        al_uop_is_16bit;    // UOP insn is_16bit signal
wire                        al_uop_rf_renb0_64; // UOP reg0 is 64-bit reg-pair
wire                        al_uop_rf_renb1_64; // UOP reg1 is 64-bit reg-pair
wire                        al_uop_prol;        // UOP inst. terms. PROL
wire                        da_uop_will_commit; // UOP inst. terms. sequence.
//wire                        al_uop_sirq;        // UOP inst. terms. SIRQ


wire                        da_uop_spoff_cg0;   // SP offset gate-enable
wire                        da_uop_dstreg_cg0;  // Dst.reg. gate-enable
wire                        da_uop_enter_cg0;   // 'enter' fsm clock enable
wire                        da_uop_enter_spi_cg0;//'enter' sp initial cg0
wire                        da_uop_enter_u7_cg0;// 'enter' u7 clock-gate (uop)
wire                        da_uop_sirq_cg0;    // 'sirq' fsm clock enable
wire                        da_uop_sirq_spi_cg0;// 'sirq' sp initial cg0
wire                        da_uop_busy_cg0;    // uop_busy clock enable
wire                        da_uop_base_cg0;    // 'base' fsm clock enable

// @reg_permissions_PROC:
//
reg                         da_ilink0_src;      // ILINK is insn. SRC
reg                         da_ilink0_dst;      // ILINK is insn. DST

// internal restart signals 
//
wire                       fch_restart_int;    // restart including retained
wire                       wa_restart;         // pipeline restart including retained
wire   [`npuarc_WA_RCMD_RANGE]    wa_restart_cmd;     // pipeline restart arguments including retained
wire fch_restart_mpd;


reg                        fch_restart_retain_r;    //ont cycle delayed fch_restart
reg                        wa_restart_retain_r;     // one cycle delayed wa_restart_r
reg    [`npuarc_WA_RCMD_RANGE]    wa_restart_cmd_retain_r; // one cycle delayed wa_restart_cmd_r

wire                       sirq_prol_retain;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Mux appropriate instruction source for predecoder                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign predecode_inst    = (db_active == 1'b1)
                           ? db_inst
                           : al_inst
                         ;



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @da_debugi_PROC: Combinatorial process to derive the condition when      //
// a prologue jump instruction should be permuted into a breakpoint.        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: da_debugi_PROC

  // Permute the terminal jump instruction of a prologue sequence when
  // DEBUGI.E mode has been set and jumping to a misaligned exception
  // vector.
  //
  permute_j_to_brk       = ar_aux_debugi_r[`npuarc_DEBUGI_E]
                         & da_uop_commit_r
                         & da_uop_prol_r
                         & da_limm_r[0]
                         ;

end // block: da_debugi_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the predecoder module to determine the next values for the   //
// register file addresses, read enables, instruction size, and limm-data   //
// detection signals.                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_predecode u_alb_predecode (
  .inst               (predecode_inst     ),
  .is_16bit           (al_is_16bit        ),
  .is_cond_inst       (al_is_cond_inst    ),
  .has_limm           (al_has_limm        ),
  .limm_r0            (al_limm_r0         ),
  .limm_r1            (al_limm_r1         ),
  .rf_ra0             (al_rf_ra0          ),
  .rf_ra1             (al_rf_ra1          ),
  .rf_renb0_64        (al_rf_renb0_64     ),
  .rf_renb1_64        (al_rf_renb1_64     ),
  .rf_renb0           (al_rf_renb0        ),
  .rf_renb1           (al_rf_renb1        )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Align Stage (AL) side micro-op sequencer logic, responsible for          //
// implementing overall control of the machine state and counter            //
// logic, and to respond to pipeline control events.                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_uop_seq_al u_alb_uop_seq_al(
  .clk                   (clk                  ),
  .rst_a                 (rst_a                ),
  .wa_restart_r          (wa_restart           ),
  .wa_restart_cmd_r      (wa_restart_cmd       ),
  .fch_restart_mpd       (fch_restart_mpd      ),
  .in_dbl_fault_excpn_r  (in_dbl_fault_excpn_r ),
  .al_inst               (al_inst              ),
  .al_pass               (al_pass              ),
//  .al_is_predicted       (al_is_predicted      ),
  .al_uop_is_enter       (al_uop_is_enter      ),
  .al_uop_do_pair        (al_uop_do_pair       ),
  .al_uop_is_irtie       (al_uop_is_irtie      ),
  .sirq_prol_retain      (sirq_prol_retain     ),
  .al_uop_sirq_haz       (al_uop_sirq_haz      ),
  .al_uop_is_ertie       (al_uop_is_ertie      ),
  .da_kill               (da_kill              ),
  .ar_aux_status32_r     (ar_aux_status32_r    ),
  .ar_aux_irq_ctrl_r     (ar_aux_irq_ctrl_r    ),
  .ar_aux_irq_ctrl_upt_r (ar_aux_irq_ctrl_upt_r),
  .irq_ctrl_wen          (irq_ctrl_wen         ),
  .ar_aux_irq_act_r      (ar_aux_irq_act_r     ),
  .int_rtie_replay_r     (int_rtie_replay_r    ),
  .ar_aux_erstatus_r     (ar_aux_erstatus_r    ),
  .ca_irq_act_nxt        (ca_irq_act_nxt       ),
  .da_uop_spoff_r        (da_uop_spoff_r       ),
  .da_uop_dstreg_r       (da_uop_dstreg_r      ),
  .da_uop_enter_r        (da_uop_enter_r       ),
  .da_uop_enter_u7_r     (da_uop_enter_u7_r    ),
  .da_uop_sirq_r         (da_uop_sirq_r        ),
  .da_uop_sirq_spi_r     (da_uop_sirq_spi_r    ),
  .da_uop_base_r         (da_uop_base_r        ),
  .da_uop_busy_r         (da_uop_busy_r        ),
  .da_uop_spoff_nxt      (da_uop_spoff_nxt     ),
  .da_uop_dstreg_nxt     (da_uop_dstreg_nxt    ),
  .da_uop_enter_nxt      (da_uop_enter_nxt     ),
  .da_uop_enter_spi_nxt  (da_uop_enter_spi_nxt ),
  .da_uop_enter_u7_nxt   (da_uop_enter_u7_nxt  ),
  .da_uop_sirq_nxt       (da_uop_sirq_nxt      ),
  .da_uop_sirq_spi_nxt   (da_uop_sirq_spi_nxt  ),
  .da_uop_base_nxt       (da_uop_base_nxt      ),
  .da_uop_busy_nxt       (da_uop_busy_nxt      ),
  .da_uop_pkilled_nxt    (da_uop_pkilled_nxt   ),
  .da_uop_pkilled_r      (da_uop_pkilled_r     ),
  .al_uop_snoops_pred    (al_uop_snoops_pred   ),
  .da_uop_pred_cg0       (da_uop_pred_cg0      )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Decode Stage (DA) side micro-op sequencer logic, responsible for         //
// emitting an encoded and partially decoded (pre-decoded) instruction      //
// as a function of the current uop_seq_al state.                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_uop_seq_da u_alb_uop_seq_da(
  .fch_restart             (fch_restart_int          ),
  .wa_restart_cmd_r        (wa_restart_cmd           ),
  .ar_aux_eret_r           (ar_aux_eret_r            ),
  .al_inst                 (al_inst                  ),
  .al_pass                 (al_pass                  ),
  .al_uop_is_enter         (al_uop_is_enter          ),
  .al_uop_do_pair          (al_uop_do_pair           ),
  .al_uop_is_irtie         (al_uop_is_irtie          ),
  .al_uop_sirq_haz         (al_uop_sirq_haz          ),
  .al_uop_is_ertie         (al_uop_is_ertie          ),
  .al_is_predicted         (al_is_predicted          ),
  .al_prediction           (al_prediction            ),
  .al_prediction_type      (al_prediction_type       ),
  .al_with_dslot           (al_with_dslot            ),
  .da_kill                 (da_kill                  ),
  .da_enable               (da_enable                ),
  .da_uop_base_r           (da_uop_base_r            ),
  .da_uop_spoff_r          (da_uop_spoff_r           ),
  .da_uop_dstreg_r         (da_uop_dstreg_r          ),
  .da_uop_enter_r          (da_uop_enter_r           ),
  .da_uop_enter_spi_r      (da_uop_enter_spi_r       ),
  .da_uop_sirq_r            (da_uop_sirq_r           ),
  .da_uop_sirq_spi_r        (da_uop_sirq_spi_r       ),
  .da_uop_busy_r            (da_uop_busy_r           ),
  .da_uop_is_predicted_r    (da_uop_is_predicted_r   ),
  .da_uop_prediction_r      (da_uop_prediction_r     ),
  .da_uop_prediction_type_r (da_uop_prediction_type_r),
  .da_uop_branch_info_r     (da_uop_branch_info_r    ),
  .da_uop_with_dslot_r      (da_uop_with_dslot_r     ),
  .da_uop_base_cg0          (da_uop_base_cg0         ),
  .da_uop_spoff_cg0         (da_uop_spoff_cg0        ),
  .da_uop_dstreg_cg0        (da_uop_dstreg_cg0       ),
  .da_uop_enter_cg0         (da_uop_enter_cg0        ),
  .da_uop_enter_spi_cg0     (da_uop_enter_spi_cg0    ),
  .da_uop_enter_u7_cg0      (da_uop_enter_u7_cg0     ),
  .da_uop_sirq_cg0          (da_uop_sirq_cg0         ),
  .da_uop_sirq_spi_cg0      (da_uop_sirq_spi_cg0     ),
  .da_uop_busy_cg0          (da_uop_busy_cg0         ),
  .al_uop_inst              (al_uop_inst             ),
  .al_uop_limm              (al_uop_limm             ),
 // .al_uop_is_16bit          (al_uop_is_16bit         ),
  .al_uop_has_limm          (al_uop_has_limm         ),
  .al_uop_limm_r0           (al_uop_limm_r0          ),
  .al_uop_limm_r1           (al_uop_limm_r1          ),
  .al_uop_rf_ra0            (al_uop_rf_ra0           ),
  .al_uop_rf_ra1            (al_uop_rf_ra1           ),
  .al_uop_rf_renb0          (al_uop_rf_renb0         ),
  .al_uop_rf_renb1          (al_uop_rf_renb1         ),
  .al_uop_rf_renb0_64       (al_uop_rf_renb0_64      ),
  .al_uop_rf_renb1_64       (al_uop_rf_renb1_64      ),
  .al_uop_is_predicted      (al_uop_is_predicted     ),
  .al_uop_prediction        (al_uop_prediction       ),
  .al_uop_prediction_type   (al_uop_prediction_type  ),
  .al_uop_branch_info       (al_uop_branch_info      ),
  .al_uop_with_dslot        (al_uop_with_dslot       ),
  .da_uop_stall             (da_uop_stall            ),
  .al_uop_pass              (al_uop_pass             ),
  .da_uop_commit            (da_uop_will_commit      ),
  .al_uop_prol              (al_uop_prol             ),

  .al_uop_epil              (al_uop_epil             )

);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic defining next predecode vector for the Decode stage  //
//                                                                          //
// The next predecode vector is provided by one of the three sources:       //
//                                                                          //
//  a). the predecoded instruction being issued by the IFU.                 //
//                                                                          //
//  b). the predecoded outputs of the uop_seq module.                       //
//                                                                          //
//  c). the output of the alb_decode module.                                //
//                                                                          //
// The uop_seq module outputs are selected when da_uop_busy is asserted.    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : da_pre_sel_PROC


  if (da_uop_busy_r)
  begin
    // Select multi-op sequencer has LIMM source
    //
    da_inst_nxt          = al_uop_inst;
    da_limm_nxt          = al_uop_limm;
  end
  else
  if (db_active)
  begin
    // Select Debugger as LIMM source
    //
    da_inst_nxt          = db_inst;
    da_limm_nxt          = db_limm;
  end
  else
  begin
    // Select IFU/Front-End as LIMM source
    //
    da_inst_nxt          = al_inst;
    da_limm_nxt          = al_limm;
  end

  if (da_uop_busy_r)
  begin
    // Select multi-op sequencer has pre-decode source
    //
    da_limm_r0_nxt       = al_uop_limm_r0;
    da_limm_r1_nxt       = al_uop_limm_r1;
    da_has_limm_nxt      = al_uop_has_limm;
    da_is_16bit_nxt      = 1'b0;
//    da_is_16bit_nxt      = al_uop_is_16bit;
    da_rf_ra0_nxt        = al_uop_rf_ra0;
    da_rf_ra1_nxt        = al_uop_rf_ra1;
    da_rf_renb0_nxt      = al_uop_rf_renb0;
    da_rf_renb1_nxt      = al_uop_rf_renb1;
    da_rf_renb0_64_nxt   = al_uop_rf_renb0_64;
    da_rf_renb1_64_nxt   = al_uop_rf_renb1_64;
    da_uop_commit_nxt    = da_uop_will_commit;
    da_uop_prol_nxt      = al_uop_prol;
    da_uop_epil_nxt      = al_uop_epil;
  end
  else
  begin
    // Select Front-End sequencer has pre-decode source
    //
    da_limm_r0_nxt       = al_limm_r0;
    da_limm_r1_nxt       = al_limm_r1;
    da_has_limm_nxt      = al_has_limm;
    da_is_16bit_nxt      = al_is_16bit;
    da_rf_ra0_nxt        = al_rf_ra0;
    da_rf_ra1_nxt        = al_rf_ra1;
    da_rf_renb0_nxt      = al_rf_renb0;
    da_rf_renb1_nxt      = al_rf_renb1;
    da_rf_renb0_64_nxt   = al_rf_renb0_64;
    da_rf_renb1_64_nxt   = al_rf_renb1_64;
    da_uop_commit_nxt    = 1'b0;
    da_uop_prol_nxt      = 1'b0;
    da_uop_epil_nxt      = 1'b0;
  end

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the Decoder to decode the current instruction                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_decode u_alb_decode(
  .inst               (da_inst_r          ),
  .pre_limm_r0        (da_limm_r0_r       ),
  .pre_limm_r1        (da_limm_r1_r       ),
  .pre_rf_renb0       (da_rf_renb0_r      ),
  .pre_rf_renb1       (da_rf_renb1_r      ),
  .pre_rf_renb0_64    (da_rf_renb0_64_r   ),
  .pre_rf_renb1_64    (da_rf_renb1_64_r   ),
  .pre_rf_ra0         (da_rf_ra0_r        ),
  .pre_rf_ra1         (da_rf_ra1_r        ),
  .aux_dbg_ub_r       (ar_aux_debug_r[28]),
  .aux_stat32_us_r    (ar_aux_status32_r[`npuarc_US_FLAG]),
  .aux_stat32_u_r     (ar_aux_status32_r[`npuarc_U_FLAG]),
  .eia_inst_valid     (eia_inst_valid     ),
  .eia_decode_src64   (eia_decode_src64   ),
  .eia_multi_cycle    (eia_multi_cycle    ),
  .eia_ra0_is_ext     (eia_ra0_is_ext     ),
  .eia_ra1_is_ext     (eia_ra1_is_ext     ),
  .eia_wa0_is_ext     (eia_wa0_is_ext     ),
  .eia_wa1_is_ext     (eia_wa1_is_ext     ),
  .eia_illegal_cond   (eia_illegal_cond   ),
  .eia_kernel         (eia_kernel         ), 
  .eia_illegal_cr_access (eia_illegal_cr_access),

  .uop_valid_r        (da_uop_busy_r      ),
  .acode              (da_code            )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process for PC-based computations in the Decode stage.     //
//                                                                          //
// This performs the computation of the next sequential PC value.           //
// The following stage directly uses sa_seq_pc_nxt and da_pc_r as link      //
// values, when that succeding stage contains a BLcc or JLcc instruction.   //
// These two values represent the link value when those BL/JL operations    //
// respectively have / have-not a delay-slot instruction.                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg     [2:0]                 da_inst_size;     // instr size, in bytes
//reg                           unused0;          // unused carry-out
reg     [`npuarc_PC_MSB:1]                da_seq_pc;        // next sequential DA PC
reg                                unused_carry;

reg     [`npuarc_PC_INC_RANGE]       inst_offset;      // inst size, excl. uops
reg                           da_pc_cg0;        // enables da_pc_r
reg                           da_limm_ignore;



always @*
begin : da_seq_pc_PROC

  //==========================================================================
  // Ignore LIMM in Instruction Size calculation when
  // (1) The Instruction is marked as Error Branch
  // (2) The Instruction is Orphaned dSlot
  // (3) The dSlot is coupled with parent in SA
  //
  da_limm_ignore  = da_error_branch_r
                  | da_orphan_dslot_r
                  ;

  //==========================================================================
  // Determine the size of the current instruction at the DA stage.
  // If the DA instr is fragmented then the da_has_limm_r signal may 
  // be incorrectly decoded and should not influence the instruction
  // size calculation.
  //
  case ({da_is_16bit_r, (da_has_limm_r & (~da_limm_ignore))})
    2'b00: da_inst_size = 3'd2;
    2'b01: da_inst_size = 3'd4;
    2'b10: da_inst_size = 3'd1;
    2'b11: da_inst_size = 3'd3;
  endcase

  //==========================================================================
  // Compute the next sequential PC address after the current DA instruction.
  //



  inst_offset     = da_uop_commit_r
                  ? `npuarc_PC_INC_BITS'd1
                  : da_inst_size
                  ;
  {unused_carry, da_seq_pc}       = da_pc_r[`npuarc_PC_MSB:1]
                  + {`npuarc_PC_INC_COMP_BITS'd0, inst_offset[`npuarc_PC_INC_RANGE]}
                  ;

  //==========================================================================
  // Set sa_seq_pc_nxt be the computed PC + instruction size, at DA.
  //
  sa_seq_pc_nxt   = da_seq_pc[`npuarc_PC_RANGE];
  
  //==========================================================================
  // Determine the speculative PC of the next instruction at the DA stage.
  //
  // The next DA-stage PC will be given by one of the following sources,
  // listed in order of precedence.
  //
  // Case  PC value       Condition
  // -------------------------------------------------------------------------
  //  (a). fch_target     fch_restart
  //
  //  (b). da_pred_bta_r  da_is_predicted_r && (da_prediction_r == `BR_TAKEN)
  //                      && (~da_dslot)
  //
  //  (c)  sa_pred_bta_r  da_in_dslot_r && sa_is_predicted_r 
  //                      && (sa_prediction_r == `BR_TAKEN)
  //
  //  (d)  sa_seq_pc_r    sa_ei_op_r - In this case we use non-predicted info
  //                      to determine that the next PC after the EI slot
  //                      instruction is the next sequential location after
  //                      the EI_S instruction currently guaranteed to be in 
  //                      the SA stage.
  //
  //  (e). sa_seq_pc_nxt  none of the above
  // -------------------------------------------------------------------------
  //
  // N.B. the dslot-tie between SA and DA is a requirement for this to work,
  // as case (d) relies on a delay-slot instruction at DA having its parent
  // branch instruction at SA when it moves forward to SA.
  //
  if (fch_restart == 1'b1)                                              // (a)
    begin
    da_pc_nxt = fch_target;
    da_pc_cg0 = 1'b1;
    end
  else if (db_active == 1'b1)                                           // (a.1)
    begin
    da_pc_nxt = ar_pc_r;
    da_pc_cg0 = da_enable & da_valid_r & (~(da_uop_busy_r));
    end
  else if (    (da_is_predicted_r == 1'b1     )                         // (b)
            && (da_prediction_r   == BR_TAKEN)
            && (da_dslot          == 1'b0     )
          )
    begin
    da_pc_nxt = da_pred_bta_r;
    da_pc_cg0 = da_enable & (~da_uop_busy_r | da_uop_commit_r);
    end
  else if (    (da_in_dslot_r     == 1'b1)                              // (c)
            && (sa_is_predicted_r == 1'b1)
            && (sa_prediction_r   == BR_TAKEN)
          )
    begin
    da_pc_nxt = sa_pred_bta_r;
    da_pc_cg0 = da_enable;
    end
  else if (sa_ei_op_r == 1'b1)                                          // (d)
    begin
    da_pc_nxt = sa_seq_pc_r;
    da_pc_cg0 = da_enable & da_valid_r;
    end
  else                                                                  // (e)
    begin
    da_pc_nxt = sa_seq_pc_nxt;
    da_pc_cg0 = da_enable & da_valid_r & (~(da_uop_busy_r));
    end
  
  //==========================================================================
  // Determine the conditions under which da_pc_r is updated.
  //
  // da_pc_cg0   = (da_enable & (~da_uop_busy_r | da_uop_commit_r)) | da_kill;
  
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process for controlling progress of the Decode stage       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : da_ctrl_PROC

  //==========================================================================
  // da_valid_nxt:  1 => Decode stage receives a valid instruction
  //  This is asserted when the Issue Pipe asserts al_pass, to
  //  indicate a valid instruction is being dispatched.
  //
  da_valid_nxt    = (   (al_pass | al_uop_pass)
                      & (~fch_restart_int)
                    )
                  | al_exception
                  | db_valid
                  ;

  //==========================================================================
  // da_valid_cg0 enables the update of da_valid_r
  //
  // da_valid_cg0 is asserted when:
  //
  //  (a). the Decode stage does not need to retain an existing instruction,
  //  (b). or, the Decode-stage instruction is killed.
  //
  // da_valid_cg0 is asserted whenever the status of the Decode stage changes,
  // and consequently all Operands-stage control registers should be enabled
  // by this signal rather than sa_enable.
  //
  da_valid_cg0    = da_enable;

  //==========================================================================
  // da_issue_cg0 enables the update of issue data registers, and is asserted
  // whenever the da_enable signal is asserted and there is an incoming
  // valid instruction or exception at DA. There is no need to update the
  // data registers if a bubble arises at DA due to an outgoing packet
  // not being replaced by an incoming packet.
  //
  da_issue_cg0    = da_enable
                  & (   al_pass
                      | al_uop_pass
                      | db_valid
                    )
                  ;

  //==========================================================================
  // da_excpn_cg0 enables the update of exception registers, and is asserted
  // whenever the da_enable signal is asserted and there is an incoming
  // exception at DA. There is no need to update the
  // exception registers if a bubble arises at DA due to an outgoing packet
  // not being replaced by an incoming packet. The da_exception_r signal
  // is controlled by the da_valid_cg0 enable, so it will update under
  // those conditions.
  //
  da_excpn_cg0    = da_enable & al_pass & al_exception;

end // block: da_ctrl_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @reg_permissions_PROC: Combinatorial process to derive the permissions   //
// associated with registers.                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: reg_permissions_PROC

  //==========================================================================
  // Insn. at DA has ILINK as a source
  //
  da_ilink0_src     = (da_rf_renb0_r & (da_rf_ra0_r == `npuarc_ILINK0_REG))
                    | (da_rf_renb1_r & (da_rf_ra1_r == `npuarc_ILINK0_REG))
                    ;

  //==========================================================================
  // Insn at DA has ILINK as a destination
  //
  da_ilink0_dst     = (da_rf_wenb0 & (da_rf_wa0 == `npuarc_ILINK0_REG))
                    | (da_rf_wenb1 & (da_rf_wa1 == `npuarc_ILINK0_REG))
                    ;

end // block: reg_permissions_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to define the ucode sent to the Operands stage      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_SA_CODE_WIDTH-1:0]      ucode_out;

always @*
begin : da_ucode_PROC

  //==========================================================================
  // Copy regfile and decode stage micro-code to micro-code output
  //
  ucode_out = da_code[`npuarc_SA_CODE_WIDTH-1:0];




  //==========================================================================
  // Set the outgoing uop_commit ucode bit if the current instruction
  // terminates a micro-op sequence.
  //
  ucode_out[`npuarc_UOP_COMMIT_RANGE] = da_uop_commit_r;
  ucode_out[`npuarc_UOP_PROL_RANGE]   = da_uop_prol_r;
  ucode_out[`npuarc_UOP_EPIL_RANGE]   = da_uop_epil_r;
  ucode_out[`npuarc_UOP_EXCPN_RANGE]  = da_uop_is_excpn_r;
  ucode_out[`npuarc_UOP_INST_RANGE]   = da_uop_valid_r;

  //==========================================================================
  // Permute the jump instruction of a prologue sequence to a BRK
  // instruction when jumping to a misaligned exception vector when
  // DEBUGI.E has been set.
  //
  if (permute_j_to_brk == 1'b1)
  begin
    ucode_out[`npuarc_JUMP_RANGE]     = 1'b0;
    ucode_out[`npuarc_BRK_OP_RANGE]   = 1'b1;
  end

  // EIA explicit destination and bflags decode
  if (eia_inst_valid)
  begin
///    ucode_out[`RF_WENB0_RANGE] = eia_dst_wen;
    ucode_out[`npuarc_Z_WEN_RANGE]    = eia_flag_wen;
    ucode_out[`npuarc_N_WEN_RANGE]    = eia_flag_wen;
    ucode_out[`npuarc_C_WEN_RANGE]    = eia_flag_wen;
    ucode_out[`npuarc_V_WEN_RANGE]    = eia_flag_wen;
  end

  // EIA explicit destination to eia dep logic
    ucode_out[`npuarc_DEST_CR_IS_EXT_RANGE] =  da_valid_r &
                                       (eia_wa0_is_ext & da_rf_wenb0 |
                                        eia_wa1_is_ext & da_rf_wenb1);

  //==========================================================================
  // Additionally apply kernel level permissions on any instruction
  // that references ILINK.
  //
  ucode_out[`npuarc_KERNEL_OP_RANGE]  = da_kernel_op
                               | (da_valid_r & (da_ilink0_src | da_ilink0_dst))
                               ;

  //==========================================================================
  // Flag instruction as a LINK referencing instruction when using
  // ILINK as a source or destination.
  //
  ucode_out[`npuarc_RGF_LINK_RANGE]   = da_valid_r & (da_ilink0_src | da_ilink0_dst)
                               ;

  //==========================================================================
  // force evaluation in x1 for eia condition code
  //
  if (da_q_field[4] == 1'b1)
    ucode_out[`npuarc_OPDS_IN_X1_RANGE] = 1'b1;

  //==========================================================================
  // Set the outgoing in_eslot ucode bit if the current instruction is in
  // the execution-slot of the SA instruction.
  //
  if (da_is_eslot == 1'b1)
    ucode_out[`npuarc_IN_ESLOT_RANGE] = 1'b1;

  //==========================================================================
  // Kill micro-code bits selectively (reduces fan-out)
  //
  if (    (da_pass == 1'b0)
       || (da_error_branch_r == 1'b1)
       || (da_iprot_viol_r & da_valid_r & (~db_active))
     )
  begin
`include "npuarc_ucode_kill_sa.v"
  end

  //==========================================================================
  // If any destination register of channel 1 is the same as a write-enabled
  // destination of channel 0, then rescind the write-enable of channel 0.
  // This takes case of, for example, LD.A R1, [R1,4], where both the loaded
  // value and the address register update target the same register.
  // The ARCv2 PRM states that the loaded value takes precedence, and therefore
  // the channel 0 write should not take place. It must be defeated in the
  // DA stage so that it does not take part in dependency checks when at SA
  // and beyond. 
  //
  if (    (da_rf_wenb0 == 1'b1)
       && (da_rf_wenb1 == 1'b1)
       && (    (da_rf_wa0 == da_rf_wa1)
            || (    da_rf_wenb1_64
                 && (da_rf_wa0[`npuarc_RGF_PAIR_RANGE] == da_rf_wa1[`npuarc_RGF_PAIR_RANGE])
                 && (da_rf_wa0[0] == 1'b1)
               )
          )
     )
  begin
     ucode_out[`npuarc_RF_WENB0_RANGE] = 1'b0;
  end

  //==========================================================================
  // Insert the ifetch speculative protection poison bit into the ucode word
  //
  ucode_out[`npuarc_IPROT_VIOL_RANGE] = da_iprot_viol_r & da_valid_r & (~db_active);

  //==========================================================================
  // Disable the prefetch ucode signal when executing debug instructions.
  //
  ucode_out[`npuarc_PREF_RANGE] = da_pref & (~db_active);

  // Disable explicit writes if APEX instructions have "no destination" attribute
  if (eia_inst_valid && !eia_dst_wen)
  begin
    ucode_out[`npuarc_RF_WENB0_RANGE]    = 1'b0;
  end

  //==========================================================================
  // Assign output to conform with established naming convention
  //
  sa_code_nxt       = ucode_out;

end

// send is_16bit to the operand stage so it can calculate commit_size
  assign sa_is_16bit_nxt = da_is_16bit_r;

//////////////////////////////////////////////////////////////////////////////
// Synchronous blocks defining decode-stage pipeline input registers        //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers for incoming control and status information, updated  //
// whenever an instruction arrives or departs this pipeline stage.          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: da_valid_regs_PROC
  if (rst_a == 1'b1)
    begin
      da_valid_r         <= 1'b0;
      da_iprot_viol_r    <= 1'b0;
    end
  else if (da_valid_cg0 == 1'b1)
    begin
      da_valid_r         <= da_valid_nxt;
      da_iprot_viol_r    <= al_iprot_viol && !da_uop_busy_r;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers for incoming pre-decoded instruction control signas,  //
// updated whenever a new instruction is issued by the IFU, or by the       //
// uop_seq module, or when a null instruction arrives. The second condition //
// ensures that the control signals return to zero when there is no valid   //
// instruction in DA.                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: da_ctrl_regs_PROC
  if (rst_a == 1'b1)
    begin
      da_rf_renb0_r    <= 1'b0;
      da_rf_renb1_r    <= 1'b0;
      da_rf_renb0_64_r <= 1'b0;
      da_rf_renb1_64_r <= 1'b0;
    end
  else if (da_issue_cg0 == 1'b1)
    begin
      da_rf_renb0_r    <= da_rf_renb0_nxt;
      da_rf_renb1_r    <= da_rf_renb1_nxt;
      da_rf_renb0_64_r <= da_rf_renb0_64_nxt;
      da_rf_renb1_64_r <= da_rf_renb1_64_nxt;
    end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers for incoming issued instruction, updated whenever a   //
// new instruction is issued by the IFU or by the in-built uop_seq module.  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: da_issue_regs_PROC
  if (rst_a == 1'b1)
    begin
      da_inst_r       <= `npuarc_DATA_SIZE'd0;
      da_limm_r       <= `npuarc_DATA_SIZE'd0;
      da_limm_r0_r    <= 1'b0;
      da_limm_r1_r    <= 1'b0;
      da_has_limm_r   <= 1'b0;
      da_is_16bit_r   <= 1'b0;
      da_rf_ra0_r     <= `npuarc_RGF_ADDR_BITS'd0;
      da_rf_ra1_r     <= `npuarc_RGF_ADDR_BITS'd0;
      da_uop_valid_r  <= 1'b0;
      da_uop_commit_r <= 1'b0;
      da_uop_prol_r   <= 1'b0;
      da_uop_epil_r   <= 1'b0;
      da_uop_is_excpn_r<= 1'b0;
      da_uop_is_sirq_r <= 1'b0;
//      da_uop_is_gpr_r  <= 1'b0;
    end
  else if (da_issue_cg0 == 1'b1)
    begin
      da_inst_r       <= da_inst_nxt;
      da_limm_r       <= da_limm_nxt;
      da_limm_r0_r    <= da_limm_r0_nxt;
      da_limm_r1_r    <= da_limm_r1_nxt;
      da_has_limm_r   <= da_has_limm_nxt;
      da_is_16bit_r   <= da_is_16bit_nxt;
      da_rf_ra0_r     <= da_rf_ra0_nxt;
      da_rf_ra1_r     <= da_rf_ra1_nxt;
      da_uop_valid_r  <= al_uop_pass;
      da_uop_commit_r <= da_uop_commit_nxt;
      da_uop_prol_r   <= da_uop_prol_nxt;
      da_uop_epil_r   <= da_uop_epil_nxt;
      da_uop_is_excpn_r<= da_uop_busy_r & da_uop_base_r[`npuarc_UOP_BASE_IS_BUSY];
      da_uop_is_sirq_r <= da_uop_busy_r & da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_BUSY];
      //we have to exclude ilink from gpr so that it can stall the pipe to wait for ilink from
      //a special ilink update at start of prologue
      //
//      da_uop_is_gpr_r  <= da_uop_sirq_r[`UOP_SIRQ_IS_GPR] 
//                        & (al_uop_rf_ra1 != (`ILINK0_REG-1))
//                        ;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous blocks defining Operand-stage pipeline input registers       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Pipeline registers for incoming instruction, updated whenever a 
// new instruction is received from the Decode stage.

always @(posedge clk or posedge rst_a)
begin: sa_inst_regs_PROC
  if (rst_a == 1'b1)
    begin
      da_pc_r         <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    end
  else if (da_pc_cg0 == 1'b1)
    begin
      da_pc_r         <= da_pc_nxt;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers for incoming exceptions, updated whenever a           //
// new exception is received from the IFU.                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: da_excpn_regs_PROC
  if (rst_a == 1'b1)
    begin
      da_excpn_type_r <= `npuarc_FCH_EXCPN_BITS'd0;
    end
  else if (da_excpn_cg0 == 1'b1)
    begin
      da_excpn_type_r <= al_excpn_type;
    end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Micro-Op sequencer state registers                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: state_reg_PROC
  if (rst_a == 1'b1)
  begin
     da_uop_base_r        <= `npuarc_UOP_BASE_BITS'd0;
    da_uop_enter_r       <= `npuarc_UOP_ENTER_BITS'd0;
    da_uop_enter_u7_r    <= 7'b0;
    da_uop_sirq_r        <= `npuarc_UOP_SIRQ_BITS'd0;
    da_uop_busy_r        <= 1'b0;
    da_uop_pkilled_r     <= 1'b0;
  end
  else
  begin
    if (da_uop_base_cg0 == 1'b1) begin
      da_uop_base_r      <= da_uop_base_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  used in submodule
      da_uop_pkilled_r   <= da_uop_pkilled_nxt;
// leda NTL_CON32 on
    end
    if (da_uop_enter_cg0 == 1'b1)
      da_uop_enter_r     <= da_uop_enter_nxt;
    if (da_uop_enter_u7_cg0 == 1'b1)
      da_uop_enter_u7_r  <= da_uop_enter_u7_nxt;
    if (da_uop_sirq_cg0 == 1'b1) begin
      da_uop_sirq_r      <= da_uop_sirq_nxt;
    end
    if (da_uop_busy_cg0 == 1'b1)
      da_uop_busy_r      <= da_uop_busy_nxt;
  end
end // block: fsm_reg_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Micro-op sequencer ancillary state                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: da_uop_enter_spi_reg_PROC

  if (rst_a == 1'b1)
    da_uop_enter_spi_r   <= `npuarc_UOP_CNT_BITS'd0;
  else if (da_uop_enter_spi_cg0 == 1'b1)
    da_uop_enter_spi_r   <= da_uop_enter_spi_nxt;

end // block: da_uop_enter_spi_reg_PROC

always @(posedge clk or posedge rst_a)
begin: da_uop_sirq_reg_PROC

  if (rst_a == 1'b1)
    da_uop_sirq_spi_r    <= `npuarc_UOP_CNT_BITS'd0;
  else if (da_uop_sirq_spi_cg0 == 1'b1)
    da_uop_sirq_spi_r    <= da_uop_sirq_spi_nxt;

end // block: da_uop_sirq_reg_PROC

always @(posedge clk or posedge rst_a)
begin: da_uop_dstreg_reg_PROC

  if (rst_a == 1'b1)
    begin
    da_uop_spoff_r        <= `npuarc_UOP_CNT_BITS'd0;
    da_uop_dstreg_r       <= `npuarc_UOP_CNT_BITS'd0;
    end
  else
    begin
    if (da_uop_spoff_cg0 == 1'b1)
      da_uop_spoff_r      <= da_uop_spoff_nxt;
    if (da_uop_dstreg_cg0 == 1'b1)
      da_uop_dstreg_r     <= da_uop_dstreg_nxt;
    end

end // block: da_uop_dstreg_reg_PROC


always @(posedge clk or posedge rst_a)
begin: da_uop_restart_PROC
  if (rst_a == 1'b1)
    begin
    fch_restart_retain_r    <= 1'b0;
    wa_restart_retain_r     <= 1'b0;
    wa_restart_cmd_retain_r <= `npuarc_WA_RCMD_BITS'd0; 
    end
  else
    begin
    if ( 1'b0
       | sirq_prol_retain
       )
      begin
        fch_restart_retain_r    <= fch_restart;
        wa_restart_retain_r     <= wa_restart_r;
        wa_restart_cmd_retain_r <= wa_restart_cmd_r;
      end
    else 
      begin
        fch_restart_retain_r    <= 1'b0;
        wa_restart_retain_r     <= 1'b0;
        wa_restart_cmd_retain_r <= `npuarc_WA_RCMD_BITS'd0; 
      end
    end
end


assign wa_restart     = wa_restart_r 
                      | wa_restart_retain_r
                      ;

assign wa_restart_cmd = wa_restart_cmd_r 
                      | wa_restart_cmd_retain_r
                      ;
assign fch_restart_int= fch_restart 
                      | fch_restart_retain_r
                      ;

assign fch_restart_mpd = fch_restart && (!fch_restart_vec);

always @(posedge clk or posedge rst_a)
begin: da_uop_pred_regs_PROC

  if (rst_a == 1'b1)
    begin
    da_uop_is_predicted_r    <= 1'b0;
    da_uop_prediction_r      <= 1'b0;
    da_uop_prediction_type_r <= `npuarc_BR_TYPE_BITS'd0;
    da_uop_branch_info_r     <= `npuarc_BR_INFO_SIZE'd0;
    da_uop_with_dslot_r      <= 1'b0;
    end
  else if (da_uop_pred_cg0 == 1'b1)
    begin
    da_uop_is_predicted_r    <= al_is_predicted;
    da_uop_prediction_r      <= al_prediction;
    da_uop_prediction_type_r <= al_prediction_type;
    da_uop_branch_info_r     <= al_branch_info;
    da_uop_with_dslot_r      <= al_with_dslot;
    end
end



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign  sa_pc_nxt       = da_pc_r;
assign  sa_limm_nxt     = da_limm_r;

assign  da_uop_u7_pcl   = da_uop_enter_u7_r[6];

assign  da_group_code   = da_inst_r[`npuarc_ISA32_GRP_RANGE];
assign  da_dop_code_32  = da_inst_r[`npuarc_ISA32_DOP_RANGE];
assign  da_sop_code_32  = da_inst_r[`npuarc_ISA32_SOP_RANGE];
assign  da_zop_code_32  = {da_inst_r[`npuarc_ISA32_ZOP_HI], da_inst_r[`npuarc_ISA32_ZOP_LO]};
assign  da_dop_code_16  = da_inst_r[`npuarc_ISA16_DOP_RANGE];
assign  da_sop_code_16  = da_inst_r[`npuarc_ISA16_SOP_RANGE];
assign  da_zop_code_16  = da_inst_r[`npuarc_ISA16_ZOP_RANGE];
assign  da_f_bit        = da_inst_r[15];

assign  da_zncv_wen     =   eia_inst_valid ? 
                          { eia_flag_wen, eia_flag_wen, eia_flag_wen, eia_flag_wen } :
                          { da_z_wen,     da_n_wen,     da_c_wen,     da_v_wen     };

assign da_rtie_op_r     =  da_code[`npuarc_RTIE_OP_RANGE];

`ifdef npuarc_RTL_PIPEMON // {
// Output for RTL pipemon.
assign Pda_limm_r   = da_limm_r;
assign Pda_is_16bit_r   = da_is_16bit_r;
assign Pda_has_limm_r   = da_has_limm_r;
assign Pda_inst_r   = da_inst_r;
`endif // }

endmodule // alb_dec_regs
