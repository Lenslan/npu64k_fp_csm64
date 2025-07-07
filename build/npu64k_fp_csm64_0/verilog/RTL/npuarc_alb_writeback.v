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
// #     #  ######   ###  #######  #######  ######      #      #####   #    #
// #  #  #  #     #   #      #     #        #     #    # #    #     #  #   #
// #  #  #  #     #   #      #     #        #     #   #   #   #        #  #
// #  #  #  ######    #      #     #####    ######   #     #  #        ###
// #  #  #  #   #     #      #     #        #     #  #######  #        #  #
// #  #  #  #    #    #      #     #        #     #  #     #  #     #  #   #
//  ## ##   #     #  ###     #     #######  ######   #     #   #####   #    #
//
//
// ===========================================================================
//
// @f:commit
//
// Description:
// @p
//  The |writeback| module implements the Writeback stage of the
//  Albacore pipeline. It follows the |commit| stage and represents the final
//  stage of the Albacore pipeline. The primary function of this stage of the
//  pipeline is to provide registered a registered interface to all write
//  operations that update state in the processor.
// @e
//
// ===========================================================================

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

module npuarc_alb_writeback (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                // Global clock
  input                       rst_a,              // Asynchronous reset signal

  ////////// Machine Architectural State /////////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]    ar_aux_status32_r,  //
  output reg                  ar_aux_user_mode_r, //
  output reg [`npuarc_PC_RANGE]      ar_pc_r,            //

  ////////// Inputs from Commit stage ////////////////////////////////////////
  //
  input                       wa_cmt_norm_evt_nxt,//
  input                       wa_cmt_uop_evt_nxt, //
  input                       wa_cmt_flag_evt_nxt,//
  input                       wa_lf_set_nxt,     //
  input                       wa_lf_clear_nxt,   //
  input                       wa_lf_double_nxt,  //
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits used
  input      [`npuarc_PADDR_RANGE]   wa_lpa_nxt,         //
  // leda NTL_CON32 on
  input  [`npuarc_WA_CODE_WIDTH-1:0] wa_code_nxt,        //
  input      [`npuarc_PC_RANGE]      ar_pc_nxt,          // next arch. PC value
  input                       ar_pc_pass,         // update architectural PC
  input      [`npuarc_PFLAG_RANGE]   wa_aux_status32_nxt,//
  input                       wa_aux_status32_pass,// Update status bits
  input                       wa_aux_flags_pass,  // update flag bits
  input                       wa_aux_uop_flag_pass,// update flag in uop seq.
  

  input     [`npuarc_RGF_ADDR_RANGE] wa_rf_wa1_nxt,      // write port 1 address
  input                       wa_rf_wenb1_nxt,    // write port 1 enable
  input                       wa_rf_wuop_nxt,     // write port is for uop load 
  input                       wa_rf_wenb1_64_nxt, // write port 1 64-bit

  input      [`npuarc_DATA_RANGE]    wa_rf_wdata0_lo_nxt,//
  input                       ca_data0_lo_pass,   // update wa_rf_wdata0_lo_r
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata1_lo_nxt,//
  input                       ca_data1_lo_pass,   // update wa_rf_wdata1_lo_r
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata0_hi_nxt,//
  input                       ca_data0_hi_pass,   // update wa_rf_wdata0_hi_r
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata1_hi_nxt,//
  input                       ca_data1_hi_pass,   // update wa_rf_wdata1_hi_r
  input                       ca_uop_active_r,    // UOP seq. is active
  input                       ca_uop_inprol_r,    //

  input                       sp_kinv_r,          //invert kernal/user mode
  input                       int_rtie_replay_r,  //force kernal mode
  input                       excpn_restart,      // restart on excpn or int

  
  ////////// Inputs from Dependency Pipeline /////////////////////////////////
  //
  input                       wa_valid_r,         //
  input                       wa_enable,          //
  input                       ca_pass,            //
  input                       ca_tail_pc_3,       //

  ////////// Inputs from Prediction Pipeline /////////////////////////////////
  //
  input                       x2_pg_xing_dslot_r, // p-xing dslot e-branch at X2
  input      [`npuarc_PC_RANGE]      mpd_pc,             // PC of X2 e-branch insn

  input                       ca_fragged_r,       // CA insn was fragged
  input                       wa_restart_kill_r,  // kill the pipe due to wa_restart

  ////////// Branch Commit Interface /////////////////////////////////////////
  //
  // Some Branch Commit interface signals are driven by alb_exu_pred_pipe
  //
  output     [`npuarc_PC_RANGE]      wa_pc,              //
  output                      wa_tail_pc_3,       //
  output                      wa_dslot,           //
  output                      wa_sleep,

  ////////// Inputs from the DMP for LLOCK and SCOND ///////////////////////////
  //
  input                       dmp_clear_lf,         // DMP detects write to LPA

  ////////// LR/SR Aux. Interface ////////////////////////////////////////////
  //
  output                      wa_sr_op_r /* verilator public_flat */,         //
  output                      wa_store_r,         //
  output                      wa_lr_op_r,         //
  output                      rtt_wa_spl_ld,      //
  input                       rtt_ca_scond,       // SCOND at CA for RTT
  input                       rtt_dc4_scond_go,   // scond will be success
  output                      rtt_wa_store,       // wa_store
  output                      wa_pref_r,          //
  output                      wa_load_r,          //
  output     [`npuarc_DATA_RANGE]    wa_sr_data_r /* verilator public_flat */,       //

  ////////// General outputs to the pipeline /////////////////////////////////
  //
  output reg [`npuarc_PFLAG_RANGE]   wa_aux_status32_r,  //

  ////////// Outputs to Dependency Pipeline //////////////////////////////////
  //
  output reg                  wa_valid_nxt,       //

  ////////// Outputs to the ZOL pipeline /////////////////////////////////////
  //
  output                      wa_wa0_lpc_r,       //
  output                      wa_loop_op_r,       //

  ////////// Accumulator interface to regfile and datapath ///////////////////
  //
  input      [`npuarc_DATA_RANGE]    ca_acch_res,        // CA-stage ACCH result   
  
  input      [`npuarc_DATA_RANGE]    accl_r,             // current ACCL register   
  input      [`npuarc_DATA_RANGE]    acch_r,             // current ACCH register   

  output reg [`npuarc_DATA_RANGE]    byp_acc_lo,         // ACCL from regfile or WA
  output reg [`npuarc_DATA_RANGE]    byp_acc_hi,         // ACCH from regfile or WA

  output reg [`npuarc_DATA_RANGE]    wa_accl_nxt,        // next implicit ACCL value
  output reg [`npuarc_DATA_RANGE]    wa_acch_nxt,        // next implicit ACCH value
  output reg                  wa_acc_wenb,        // implicit ACC write enb
  
  /////////// special register writeback  ////////////////////////////////////
  //
  output                      wa_uopld_jli_base,
  output                      wa_uopld_ldi_base,
  output                      wa_uopld_ei_base,
  output                      wa_uopld_lp_count,
  output                      wa_uopld_lp_start,
  output                      wa_uopld_lp_end,
  output                      wa_uopld_status32,

  output [`npuarc_DATA_RANGE]        wa_uopld_data,

  ////////// Outputs from Writeback stage ////////////////////////////////////
  //
  output reg                  wa_cmt_norm_evt_r /* verilator public_flat */,  //
  output reg                  wa_cmt_flag_evt_r,  //
  output reg [`npuarc_DATA_RANGE]    wa_rf_wdata0_hi_r,  // channel 0 write data[63:32]
  output                      wa_rf_wenb0_64_r,   // enable channel 0 [63:32]
  output                      wa_cc_byp_64_haz_r, // WA insn cannot bypass r0h
  output     [`npuarc_RGF_ADDR_RANGE]wa_rf_wa0_r,        // channel 0 write address
  output reg [`npuarc_DATA_RANGE]    wa_rf_wdata0_lo_r,  // channel 0 write data[31:0]
  output                      wa_rf_wenb0_r,      // enable channel 0 [31:0]
  output reg [`npuarc_DATA_RANGE]    wa_rf_wdata1_hi_r,  // channel 1 write data[63:32]
  output reg                  wa_rf_wenb1_64_r,   // enable channel 1 [63:32]
  output                      wa_writes_acc_r,    //
  output                      wa_acc_wenb_r,      //
  output reg                  wa_lock_flag_r,     // LF, for LLOCK/SCOND
  output reg                  wa_lock_double_r,   // Size of lock
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
  output reg [`npuarc_PADDR_RANGE]   wa_lpa_r,           // LPA, for LLOCK/SCOND
  // leda NTL_CON32 on
  output reg [`npuarc_RGF_ADDR_RANGE]wa_rf_wa1_r,        // channel 1 write address
  output reg [`npuarc_DATA_RANGE]    wa_rf_wdata1_lo_r,  // channel 1 write data[31:0]
  input                       smt_cap_rst_vec,
  output reg [`npuarc_PC_RANGE]      ar_pc_save_r,
  input                       ar_save_clk,
  output reg                  ar_save_en_r,




  output reg                  wa_rf_wenb1_r      // enable channel 1 [31:0]
);

// @wa_ctrl_PROC
//
reg                           ar_pc_cg0;
reg                           wa_pc_cg0;
reg                           wa_aux_status32_cg0;
reg                           wa_aux_flags_cg0;
reg                           wa_code_cg0;
reg                           wa_write0_lo_cg0;
reg                           wa_write1_lo_cg0;
reg                           wa_write0_hi_cg0;
reg                           wa_write1_hi_cg0;

// @wa_aux_status32_reg_PROC
//
// @wa_ctrl_regs_PROC
//

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                           wa_cmt_uop_evt_r /* verilator public_flat */;//@@TB use this signal
reg [`npuarc_WA_CODE_WIDTH-1:0]      wa_code_r;
// leda NTL_CON32 on
reg                           wa_rf_wuop_r;
reg                           wa_uop_de_flag_r;

// @wa_pc_reg_PROC
//
reg [`npuarc_PC_RANGE]               wa_pc_r /* verilator public_flat */;            // PC of WA-stage instruction
reg                           wa_tail_pc_3_r;     // bit 4 of br tail PC

reg [`npuarc_DATA_RANGE]             wa_acch_r;          // ACCH at WA

// @wa_lf_PROC
//
reg                           wa_lock_flag_nxt;   // LF, for LLOCK/SCOND
reg                           wa_lock_double_cg0;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  ucode generated
// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

assign wa_rf_wa0_r  = wa_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign wa_rf_wenb0_r  = wa_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign wa_rf_wenb0_64_r  = wa_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
assign wa_cc_byp_64_haz_r  = wa_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
wire   wa_has_limm_r;  // generated code
assign wa_has_limm_r  = wa_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   wa_is_16bit_r;  // generated code
assign wa_is_16bit_r  = wa_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign wa_sr_op_r   = wa_code_r[`npuarc_SR_OP_RANGE];  // generated code
assign wa_loop_op_r  = wa_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
wire   wa_locked_r;  // generated code
assign wa_locked_r  = wa_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign wa_wa0_lpc_r  = wa_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
wire   wa_dslot_r;  // generated code
assign wa_dslot_r  = wa_code_r[`npuarc_DSLOT_RANGE];  // generated code
wire   wa_sleep_op_r;  // generated code
assign wa_sleep_op_r  = wa_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
assign wa_acc_wenb_r  = wa_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
assign wa_writes_acc_r  = wa_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign wa_lr_op_r   = wa_code_r[`npuarc_LR_OP_RANGE];  // generated code
wire   wa_jump_r;  // generated code
assign wa_jump_r  = wa_code_r[`npuarc_JUMP_RANGE];  // generated code
assign wa_load_r    = wa_code_r[`npuarc_LOAD_RANGE];  // generated code
assign wa_pref_r    = wa_code_r[`npuarc_PREF_RANGE];  // generated code
assign wa_store_r   = wa_code_r[`npuarc_STORE_RANGE];  // generated code
wire   wa_uop_prol_r;  // generated code
assign wa_uop_prol_r  = wa_code_r[`npuarc_UOP_PROL_RANGE];  // generated code

// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: wa_ctrl_PROC

  //==========================================================================
  // There will be a valid instruction at the WA stage in the next cycle
  // if the ca_pass signal is asserted in the current cycle.
  //
  wa_valid_nxt          = ca_pass;

  //==========================================================================
  // Register update control signals for STATUS32, flags, architectural PC,
  // and current PC of the WA-stage instruction.
  //
  wa_aux_status32_cg0   = (wa_enable & wa_aux_status32_pass);
  wa_aux_flags_cg0      = wa_enable & wa_aux_flags_pass;
  ar_pc_cg0             = wa_enable & ar_pc_pass;

  wa_pc_cg0             = wa_enable 
                        & (   ar_pc_pass
                            | excpn_restart
                            | (ca_fragged_r & (!wa_restart_kill_r))
                            | x2_pg_xing_dslot_r
                          )
                        ;

  //==========================================================================
  // Register update control signals for registers carrying result channel 0.
  //
  wa_write0_lo_cg0      = wa_enable & ca_data0_lo_pass;
  wa_write0_hi_cg0      = wa_enable & ca_data0_hi_pass;

  //==========================================================================
  // Register update control signals for registers carrying result channel 1.
  //
  wa_write1_lo_cg0      = wa_enable & ca_data1_lo_pass;
  wa_write1_hi_cg0      = wa_enable & ca_data1_hi_pass;
  
  //==========================================================================
  // wa_code_cg0 enables the update of the wa_code_r register.
  //
  // wa_code_cg0 is asserted when:
  //
  //  (a). the WA stage is enabled to receive new input, and
  //  (b). either wa_valid_r or wa_valid_nxt (i.e. ca_pass)
  //
  // Condition (b) ensures that the WA ucode vector is updated whenever a
  // new instruction arrives or an exising instruction leaves. It does not
  // clock the ucode vector when it is already empty and nothing is arriving,
  // nor if it is full but not exiting WA.
  //
  wa_code_cg0     = wa_enable & (wa_valid_r | ca_pass)
                  | wa_code_nxt[`npuarc_WRITES_ACC_RANGE]
                  | wa_writes_acc_r
                  ;

  //==========================================================================
  //
  byp_acc_lo      = wa_acc_wenb_r ? wa_rf_wdata0_lo_r : accl_r;
  byp_acc_hi      = wa_acc_wenb_r ? wa_acch_r         : acch_r;

  //==========================================================================
  // Determine the next values to be assigned to ACCL and ACCH by implicit
  // instruction update (e.g. by MAC operations).
  //
  wa_accl_nxt     = wa_rf_wdata0_lo_r;
  wa_acch_nxt     = wa_acch_r;
  wa_acc_wenb     = wa_acc_wenb_r;

end // block: wa_ctrl_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Implement mapping between STATUS32 packed register format to the       //
// true architectural format for distribution throughout the RTL.         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: ar_PROC

  ar_aux_status32_r                    = `npuarc_DATA_SIZE'd0;
  ar_aux_status32_r[`npuarc_H_FLAG]           = wa_aux_status32_r[`npuarc_P_H_FLAG];
  ar_aux_status32_r[`npuarc_E_FLAG]           = wa_aux_status32_r[`npuarc_P_E_FLAG];
  ar_aux_status32_r[`npuarc_AE_FLAG]          = wa_aux_status32_r[`npuarc_P_AE_FLAG];
  ar_aux_status32_r[`npuarc_DE_FLAG]          = wa_aux_status32_r[`npuarc_P_DE_FLAG];
  ar_aux_status32_r[`npuarc_U_FLAG]           = wa_aux_status32_r[`npuarc_P_U_FLAG];
  ar_aux_status32_r[`npuarc_ZNCV_RANGE]       = wa_aux_status32_r[`npuarc_P_ZNCV_FLAG];
  ar_aux_status32_r[`npuarc_L_FLAG]           = wa_aux_status32_r[`npuarc_P_L_FLAG];
  ar_aux_status32_r[`npuarc_DZ_FLAG]          = wa_aux_status32_r[`npuarc_P_DZ_FLAG];
  ar_aux_status32_r[`npuarc_SC_FLAG]          = wa_aux_status32_r[`npuarc_P_SC_FLAG];
  ar_aux_status32_r[`npuarc_ES_FLAG]          = wa_aux_status32_r[`npuarc_P_ES_FLAG];
  ar_aux_status32_r[`npuarc_AD_FLAG]          = wa_aux_status32_r[`npuarc_P_AD_FLAG];
  ar_aux_status32_r[`npuarc_US_FLAG]          = wa_aux_status32_r[`npuarc_P_US_FLAG];
  ar_aux_status32_r[`npuarc_EIH_FLAG]         = wa_aux_status32_r[`npuarc_P_EIH_FLAG];
  ar_aux_status32_r[`npuarc_IE_FLAG]          = wa_aux_status32_r[`npuarc_P_IE_FLAG];
  
    // When a multi-op sequence is active (as a consequence of either an
    // exception or an interrupt prologue) we may legitimately be
    // operating within a D-/E-Slot position. We wish to override this
    // fact such that the prediction logic does not become confused by
    // the fact that the terminal jump instruction appears in a
    // slot. This is a consequence of the fact that STATUS32 is not
    // updated until the completion/committal of the prologue sequence.
    //
    if (ca_uop_inprol_r == 1'b1)
    begin
      ar_aux_status32_r[`npuarc_DE_FLAG]    = 1'b0;
      ar_aux_status32_r[`npuarc_ES_FLAG]    = 1'b0;
    // for firq we switch reg bank to 1 during prologue sequence
    // for prologue to save context (sp) to back 1
    //
    end
    else if (ca_uop_active_r) begin
    // the DE flag is useful for the leave instruction during epilogue sequence
    // As DE_FLAG is only affected usefule by leave instruction during uop sequence
    // we can sllow it pass around in any uop sequence 
    //
      ar_aux_status32_r[`npuarc_DE_FLAG]    = wa_uop_de_flag_r;
    end 

    //U_FLAG inversion
    // During interrupt prologue UOP sequence we need to be in kernal mode to run aex
    // for arch. user mode (user -> kernal)
    // During interrupt epilogue UOP we need run aex to recover back to user SP
    // we need user mode to tell UOP fsm to do aex (kernal -> user) 
    //
    ar_aux_status32_r[`npuarc_U_FLAG]      = (wa_aux_status32_r[`npuarc_P_U_FLAG] ^ sp_kinv_r)
                                    & (!int_rtie_replay_r);

    // This is the actual arch. U_FLAG as opposed to ar_aux_status32_r[`U_FLAG]
    // They may not be the same during uop sequence due to sp_kinv_r
    //
    ar_aux_user_mode_r              = wa_aux_status32_r[`npuarc_P_U_FLAG];

//register bank pointer
//it goes to regfile and select the banked registers
//

end // block: ar_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Implement the next state of the Lock Flag (LF) for use by LLOCK, SCOND //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: wa_lf_PROC

  // LF is set when an LLOCK is committing in the current cycle, as signalled
  // by the assertion of wa_lf_set_nxt
  //
  // LF is retained unless one of the following three events occurs:
  //
  //   1. wa_lf_clear_nxt is asserted, indicating that we are retiring an 
  //      SCOND instruction, or committing an SCOND instruction in order 
  //      without performing a write;
  //   2. if an interrupt/exception prologue completes in the Writeback stage;
  //   3. of if the DMP detects a write to the LPA register from this, or 
  //      any other processor or bus master, at any time.
  //
  wa_lock_flag_nxt  = (wa_lf_set_nxt | wa_lock_flag_r)
                    & (~wa_lf_clear_nxt)              // (1)
                    & (~wa_uop_prol_r)                // (2)
                    & (~dmp_clear_lf)                 // (3)
                    ;

  // The lock size only changes when a new lock is being set-up
  //
  wa_lock_double_cg0 = wa_lf_set_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous blocks for architectural state updates                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: wa_aux_status32_reg_PROC
  if (rst_a == 1'b1) begin
    wa_aux_status32_r <= {`npuarc_P_CLEAR_BITS'd0, 1'b`npuarc_HALT_ON_RESET, `npuarc_ZNCV_BITS'd0};
    wa_uop_de_flag_r  <= 1'b0;
  end
  // Release any pending instruction on NMI
  else begin
    if (wa_aux_status32_cg0 == 1'b1) begin
        wa_aux_status32_r[`npuarc_PSTATUS_RANGE] <= wa_aux_status32_nxt[`npuarc_PSTATUS_RANGE];
    end
  
    if (wa_aux_flags_cg0 == 1'b1) begin
      wa_aux_status32_r[`npuarc_P_ZNCV_FLAG]   <= wa_aux_status32_nxt[`npuarc_P_ZNCV_FLAG];
    end
    
    if (wa_aux_uop_flag_pass) begin
      wa_uop_de_flag_r                  <= wa_aux_status32_nxt[`npuarc_P_DE_FLAG];
    end

  end
end // block: wa_aux_status32_reg_PROC

always @(posedge clk or posedge rst_a)
begin : ar_pc_reg_PROC
  if (rst_a == 1'b1)
    begin
    ar_pc_r        <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    end
  else if (ar_pc_cg0 == 1'b1)
    begin
    ar_pc_r        <= ar_pc_nxt;
    end
end
// Saved AR PC to be used after reset for SMART
//
always @(posedge clk or posedge rst_a)
begin : ar_save_en_reg_PROC
  if (rst_a == 1'b1)
    ar_save_en_r    <= 1'b0;
  else begin
    if (smt_cap_rst_vec == 1'b1)
      ar_save_en_r  <= 1'b0;
    else 
      ar_save_en_r  <= ar_pc_cg0;
  end
end // block : ar_save_en_reg_PROC
//
// spyglass disable_block STARC-2.3.4.3
// SMD: (Recommended) Flip-flop has neither asynchronous set nor asynchronous reset
// SJ:  The intention of this register is to retain its value during reset
// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected 
// SJ:  AR_PC_SAVE is meant for debugging only; Data corruption is rare.
always @(posedge ar_save_clk)
begin : ar_pc_save_reg_PROC
  ar_pc_save_r       <= ar_pc_r;
end
// spyglass enable_block Ar_resetcross01
// spyglass enable_block STARC-2.3.4.3
//

always @(posedge clk or posedge rst_a)
begin : wa_br_commit_reg_PROC
  if (rst_a == 1'b1)
    begin
    wa_pc_r         <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    wa_tail_pc_3_r  <= 1'b0;
    end
  else if (wa_pc_cg0 == 1'b1)
    begin
    wa_pc_r         <= x2_pg_xing_dslot_r
                     ? mpd_pc
                     : ar_pc_r
                     ;
    wa_tail_pc_3_r  <= ca_tail_pc_3;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: wa_rf_regs_PROC

  if (rst_a == 1'b1)
    begin
    wa_rf_wdata0_lo_r <= `npuarc_DATA_SIZE'd0;
    wa_rf_wdata1_lo_r <= `npuarc_DATA_SIZE'd0;
    wa_rf_wdata0_hi_r <= `npuarc_DATA_SIZE'd0;
    wa_rf_wdata1_hi_r <= `npuarc_DATA_SIZE'd0;
    wa_acch_r         <= `npuarc_DATA_SIZE'd0;
    end
  else
    begin
    if (wa_write0_lo_cg0 == 1'b1)
      wa_rf_wdata0_lo_r <= wa_rf_wdata0_lo_nxt;

    if (wa_write0_hi_cg0 == 1'b1)
      wa_rf_wdata0_hi_r <= wa_rf_wdata0_hi_nxt;

    if (wa_write1_lo_cg0 == 1'b1)
      wa_rf_wdata1_lo_r <= wa_rf_wdata1_lo_nxt;

    if (wa_write1_hi_cg0 == 1'b1)
      wa_rf_wdata1_hi_r <= wa_rf_wdata1_hi_nxt;

    wa_acch_r          <= ca_acch_res;
    end
end

always @(posedge clk or posedge rst_a)
begin: wa_code_regs_PROC
  if (rst_a == 1'b1)
    wa_code_r            <= `npuarc_WA_CODE_WIDTH'd0;
  else if (wa_code_cg0 == 1'b1)
    wa_code_r            <= wa_code_nxt;
end





always @(posedge clk or posedge rst_a)
begin: wa_ctrl_regs_PROC
  if (rst_a == 1'b1)
  begin
    wa_cmt_norm_evt_r    <= 1'b0;
    wa_cmt_flag_evt_r    <= 1'b0;
    wa_cmt_uop_evt_r     <= 1'b0;

    wa_rf_wa1_r          <= `npuarc_RGF_ADDR_BITS'd0;
    wa_rf_wenb1_r        <= 1'b0;
    wa_rf_wuop_r         <= 1'b0;
    wa_rf_wenb1_64_r     <= 1'b0;
  end
  else
    begin
// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low 
// SJ:  Done on purpose
      if (wa_enable == 1'b1)
        begin
        wa_cmt_norm_evt_r    <= wa_cmt_norm_evt_nxt;
        wa_cmt_uop_evt_r     <= wa_cmt_uop_evt_nxt;
        wa_cmt_flag_evt_r    <= wa_cmt_flag_evt_nxt;
// spyglass enable_block FlopEConst
        // The following signals carry the write port 1 write enable signals.
        // These update not only when an instruction commits, but also
        // when a value is retired out-of-order. These registers are also
        // updated in order to clear them back to zero after each operation
        // as been performed.
        //
        wa_rf_wenb1_r        <= wa_rf_wenb1_nxt;
        wa_rf_wuop_r         <= wa_rf_wuop_nxt;
        wa_rf_wenb1_64_r     <= wa_rf_wenb1_64_nxt;
        end
        
      // The write register addres for port 1 updates whenever there is
      // a valid write for port 1, indicated by wa_write1_lo_cg0.
      // 
      if (wa_write1_lo_cg0 == 1'b1)
        wa_rf_wa1_r          <= wa_rf_wa1_nxt;
  end
end // block: wa_ctrl_regs_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Implement the Lock Flag (LF) for use by LLOCK, SCOND                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: wa_lf_reg_PROC
  if (rst_a == 1'b1)
  begin
    wa_lock_flag_r   <= 1'b0;
    wa_lock_double_r <= 1'b0;
  end  
  else
  begin
    wa_lock_flag_r     <= wa_lock_flag_nxt;
    
    if (wa_lock_double_cg0)
    begin
      wa_lock_double_r <= wa_lf_double_nxt;
    end
  end    
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Implement the Lock Physical Address (LPA) for use by LLOCK, SCOND      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: wa_lpa_reg_PROC
  if (rst_a == 1'b1)
    wa_lpa_r <= `npuarc_PADDR_SIZE'd0;
  else if (wa_lf_set_nxt == 1'b1)
    wa_lpa_r <= wa_lpa_nxt;
end
reg rtt_wa_scond_clr_r;
always @(posedge clk or posedge rst_a)
begin: wa_scond_clr_reg_PROC
  if (rst_a == 1'b1)
    rtt_wa_scond_clr_r <= 1'b0;
  else 
    rtt_wa_scond_clr_r <= (rtt_ca_scond & (~rtt_dc4_scond_go));
end // block : wa_scond_clr_reg_PROC




assign  rtt_wa_spl_ld     = 1'b0
                    | wa_uopld_jli_base
                    | wa_uopld_ldi_base
                    | wa_uopld_ei_base
                    | wa_uopld_lp_count
                    | wa_uopld_lp_start
                    | wa_uopld_lp_end
                    | wa_uopld_status32
                    ;


assign rtt_wa_store      = wa_store_r 
                         & (~rtt_wa_scond_clr_r)
                         ;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// upload aux registers during interrupt epilogue                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign  wa_uopld_jli_base = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_JLI_BASE_REG);
assign  wa_uopld_ldi_base = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_LDI_BASE_REG);
assign  wa_uopld_ei_base  = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_EI_BASE_REG);
assign  wa_uopld_lp_count = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_LP_COUNT_REG);
assign  wa_uopld_lp_start = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_LP_START_REG);
assign  wa_uopld_lp_end   = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_LP_END_REG);
assign  wa_uopld_status32 = wa_rf_wuop_r & (wa_rf_wa1_r == `npuarc_REG_STATUS32);

assign  wa_uopld_data     = wa_rf_wdata1_lo_r;
 
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Assignment of output wires                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign wa_pc              = wa_pc_r;                          // branch PC
assign wa_tail_pc_3       = wa_tail_pc_3_r;                   // br tail addr
assign wa_dslot           = wa_dslot_r;                       // insn has dslot
// inst size

assign wa_sr_data_r       = wa_rf_wdata1_lo_r;
assign wa_sleep           = wa_sleep_op_r;

endmodule // alb_writeback
