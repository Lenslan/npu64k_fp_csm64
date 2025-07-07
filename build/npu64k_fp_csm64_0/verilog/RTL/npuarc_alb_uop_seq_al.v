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


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_uop_seq_al (
  ////////// General input signals /////////////////////////////////////////
  //
  input                        clk,                 // Processor clock
  input                        rst_a,               // Asynchronous reset

  ////////// Global Restart ////////////////////////////////////////////////
  //
  input                        wa_restart_r,        // pipeline restart
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_WA_RCMD_RANGE]       wa_restart_cmd_r,    // pipeline restart arguments
// leda NTL_CON13C on
// leda NTL_CON37 on
  input                        fch_restart_mpd,
  input                        in_dbl_fault_excpn_r, // In double fault
  ////////// Align Stage control signals ///////////////////////////////////
  //
  input [`npuarc_DATA_RANGE]          al_inst,             // AL-stage aligned inst.
  input                        al_pass,             // AL-stage valid

  output reg                   al_uop_is_enter,     //
  output reg                   al_uop_do_pair,      //
  output reg                   al_uop_is_irtie,     // AL is Intrupt. RTIE
  output reg                   sirq_prol_retain,    // to control cg0 for sirq_r
  output reg                   al_uop_sirq_haz,     // to disable int_req
  output reg                   al_uop_is_ertie,     // AL is Excpn RTIE

  ////////// Decode Stage control signals //////////////////////////////////
  //
  input                        da_kill,             // DA-stage kill

  ////////// Architecturally-committed state ////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_DATA_RANGE]          ar_aux_status32_r,   // STATUS32 aux register
// leda NTL_CON13C on
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_DATA_RANGE]          ar_aux_irq_ctrl_r,   // IRQ_CTRL aux register
// leda NTL_CON13C on
  input                        ar_aux_irq_ctrl_upt_r, // IRQ_CTRL updt.
  input                        irq_ctrl_wen,        //IRQ_CTRL write pulse
  input [`npuarc_DATA_RANGE]          ar_aux_irq_act_r,    // IRQ_ACT aux register
  input                        int_rtie_replay_r,   // force kernal mode 
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_DATA_RANGE]          ar_aux_erstatus_r,   // ERSTATUS aux register

  ////////// Machine Preemption state transition ///////////////////////////
  //
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input [`npuarc_DATA_RANGE]          ca_irq_act_nxt,      // Next IRQ_ACT state.
  // leda NTL_CON37 on
// leda NTL_CON13C on
  ////////// FSM state vectors from DA /////////////////////////////////////
  //
  input [`npuarc_UOP_CNT_RANGE]       da_uop_spoff_r,      //
  input [`npuarc_UOP_CNT_RANGE]       da_uop_dstreg_r,     //
  input [`npuarc_UOP_SIRQ_RANGE]      da_uop_enter_r,      // UOP 'enter' state reg.
  input [6:0]                  da_uop_enter_u7_r,   // UOP 'enter' u7 oprnd.
  input [`npuarc_UOP_SIRQ_RANGE]      da_uop_sirq_r,       // UOP 'sirq' state reg.
  input [`npuarc_UOP_CNT_RANGE]       da_uop_sirq_spi_r,   //
  input [`npuarc_UOP_BASE_RANGE]      da_uop_base_r,       // UOP baseline state reg.
  input                        da_uop_busy_r,       //

  ////////// FSM state vectors to DA /////////////////////////////////////
  //
  output reg [`npuarc_UOP_CNT_RANGE]  da_uop_spoff_nxt,    // UOP SP-offset
  output reg [`npuarc_UOP_CNT_RANGE]  da_uop_dstreg_nxt,   // GPR reg. index

  output reg [`npuarc_UOP_SIRQ_RANGE] da_uop_enter_nxt,    // UOP 'enter' state reg.
  output reg [`npuarc_UOP_CNT_RANGE]  da_uop_enter_spi_nxt,// UOP 'enter' sp offset
  output reg [6:0]             da_uop_enter_u7_nxt, // UOP 'enter' u7 oprnd
  output reg [`npuarc_UOP_SIRQ_RANGE] da_uop_sirq_nxt,     // UOP 'sirq' state reg.
  output reg [`npuarc_UOP_CNT_RANGE]  da_uop_sirq_spi_nxt, //
  output reg [`npuarc_UOP_BASE_RANGE] da_uop_base_nxt,     // UOP baseline state reg.
  output reg                   da_uop_busy_nxt,     // UOP busy nxt state
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  used correctly
  output reg                   da_uop_pkilled_nxt,  // prologue is killed by exception
  // leda NTL_CON32 on
  input                        da_uop_pkilled_r,    //
  ////////// BPU interface ///////////////////////////////////////////////
  //
  output reg                   al_uop_snoops_pred,  //
  output reg                   da_uop_pred_cg0      //
  );

// Global definitions
//

// @fsm_irq_control_PROC
//
reg                           irq_rtrn_to_u;
reg [`npuarc_UOP_CNT_RANGE]          irq_gpr_max;
reg                           irq_gpr_nz;
reg                           irq_dstreg_ne;
reg                           irq_doblink;

// @fsm_enter_control_PROC
//
reg [`npuarc_UOP_CNT_RANGE]          enter_dstreg_max;
reg                           enter_dstreg_ne;
reg [`npuarc_UOP_CNT_RANGE]          dstreg_max;
// @decode_PROC
//
reg                           al_inst_is_rtie;
reg                           al_enter_is_illegal;
reg                           al_inst_is_enter;
reg                           al_enter_op;

// @sirq_sp_init_nxt_PROC
//
reg [1:0]                     sirq_sp_cntrl_nxt;

// @cmd_PROC
//
reg                           sirq_prol;
reg                           sirq_epil;

reg                           excpn_prol;
reg                           excpn_epil;
reg                           reset_prol;

// @uop_busy_PROC
//
reg                           da_uop_busy_set;
reg                           da_uop_busy_prmpt;
reg                           da_uop_busy_clr;
reg                           da_uop_epil_busy_set;

// @da_uop_pred_cg0
//
reg                           expect_pred;


// @sirq_sp_cntrl_reg_PROC
//
reg [1:0]                     sirq_sp_cntrl_r;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused carry bit
reg                           dont_care_0;
reg                           dont_care_1;
// leda NTL_CON13A on
reg                           da_uop_epil_busy_nxt;     // UOP epilogue busy nxt state
reg                           da_uop_epil_busy_r;       // UOP epilogue busy state
 
// leda W175 off
// LMD: parameter has been defined but not used
// LJ:  not all parameters are used in all configurations
parameter FSM_BASE_S0       =    `npuarc_UOP_BASE_BITS'b00000_00;
parameter FSM_BASE_EXCPNP0  =    `npuarc_UOP_BASE_BITS'b10000_10;
parameter FSM_BASE_EXCPNP1  =    `npuarc_UOP_BASE_BITS'b11001_11;
parameter FSM_BASE_RESET0   =    `npuarc_UOP_BASE_BITS'b11101_11;
parameter FSM_BASE_EXCPNE0  =    `npuarc_UOP_BASE_BITS'b10010_10;
parameter FSM_BASE_EXCPNE1  =    `npuarc_UOP_BASE_BITS'b11011_11;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @da_uop_base_nxt_PROC:                                                   //
//                                                                          //
// Process to derive the next-state update to the 'base'                    //
// state-machine.                                                           //
// We keep the "da_uop_xkilled" signal during the excpetion that identifies //
// the killed prologue or epilogue by the exception.                        //
// They change the methods of exit for the exception.                       // 
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: da_uop_base_nxt_PROC

  //==========================================================================
  // Assign defaults
  //
  da_uop_base_nxt        = da_uop_base_r;
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  used correctly
  da_uop_pkilled_nxt     = da_uop_pkilled_r;
  // leda NTL_CON32 on
  //==========================================================================
  //
  //
  case (da_uop_base_r)
    FSM_BASE_S0: begin
       if (reset_prol)
       begin
          da_uop_base_nxt    = FSM_BASE_RESET0;
       end
       else
       if (excpn_prol)
       begin
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  used correctly
          da_uop_pkilled_nxt = wa_restart_cmd_r[`npuarc_RSRT_IS_PKILL];
  // leda NTL_CON32 on
          if (ar_aux_status32_r[`npuarc_U_FLAG] && (~in_dbl_fault_excpn_r))
            da_uop_base_nxt  = FSM_BASE_EXCPNP0;
          else
            da_uop_base_nxt  = FSM_BASE_EXCPNP1;
        end
        else
        if (excpn_epil)
        begin
          if (ar_aux_erstatus_r[`npuarc_U_FLAG] == 1'b1)
            da_uop_base_nxt = FSM_BASE_EXCPNE0;
          else
            da_uop_base_nxt = FSM_BASE_EXCPNE1;
        end
    end
    FSM_BASE_EXCPNP0:
      da_uop_base_nxt  = FSM_BASE_EXCPNP1;
    FSM_BASE_EXCPNE0:
      da_uop_base_nxt  = FSM_BASE_EXCPNE1;

    FSM_BASE_EXCPNP1: begin
      da_uop_base_nxt  = FSM_BASE_S0;
    end
    FSM_BASE_EXCPNE1: begin
      da_uop_base_nxt  = FSM_BASE_S0;
    end
    FSM_BASE_RESET0:
      da_uop_base_nxt  = FSM_BASE_S0;

// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept

    default: ;
  endcase // case (da_uop_base_r)

  //==========================================================================
  // State-transition override on restart
  //
  casez ({   wa_restart_r & (~reset_prol)
           , (excpn_prol)
           , (ar_aux_status32_r[`npuarc_U_FLAG] && (~in_dbl_fault_excpn_r))
         })
    3'b1_0?: da_uop_base_nxt  = FSM_BASE_S0;
    3'b1_10: da_uop_base_nxt  = FSM_BASE_EXCPNP1;
    3'b1_11: da_uop_base_nxt  = FSM_BASE_EXCPNP0;
    default: ;
  endcase
  
end // block: uop_base_nxt_PROC



parameter FSM_SIRQ_S0      =     `npuarc_UOP_SIRQ_BITS'b0000_00_0000; // IDLE

parameter FSM_PROL_S1      =     `npuarc_UOP_SIRQ_BITS'b1000_00_1000; // AEX
parameter FSM_PROL_S2      =     `npuarc_UOP_SIRQ_BITS'b1000_10_0000; // STAT32
parameter FSM_PROL_S3      =     `npuarc_UOP_SIRQ_BITS'b1000_10_0001; // PC
parameter FSM_PROL_S4      =     `npuarc_UOP_SIRQ_BITS'b1000_10_0010; // BLINK
parameter FSM_PROL_S5      =     `npuarc_UOP_SIRQ_BITS'b1000_10_0011; // R30
parameter FSM_PROL_S7      =     `npuarc_UOP_SIRQ_BITS'b1000_11_0000; // GPR
parameter FSM_PROL_S8      =     `npuarc_UOP_SIRQ_BITS'b1000_00_1010; // SP
parameter FSM_PROL_S9      =     `npuarc_UOP_SIRQ_BITS'b1000_00_1001; // AEX
parameter FSM_PROL_S10     =     `npuarc_UOP_SIRQ_BITS'b1101_00_1011; // J limm
parameter FSM_PROL_S11     =     `npuarc_UOP_SIRQ_BITS'b1000_10_0100; // LP_COUNT
parameter FSM_PROL_S12     =     `npuarc_UOP_SIRQ_BITS'b1000_10_0101; // LP_START
parameter FSM_PROL_S13     =     `npuarc_UOP_SIRQ_BITS'b1000_10_0110; // LP_END
parameter FSM_PROL_S14     =     `npuarc_UOP_SIRQ_BITS'b1000_10_0111; // JLI_BASE
parameter FSM_PROL_S15     =     `npuarc_UOP_SIRQ_BITS'b1000_10_1000; // LDI_BASE
parameter FSM_PROL_S16     =     `npuarc_UOP_SIRQ_BITS'b1000_10_1001; // EI_BASE
parameter FSM_PROL_S17     =     `npuarc_UOP_SIRQ_BITS'b1000_10_1100; // LP_COUNT
parameter FSM_PROL_S18     =     `npuarc_UOP_SIRQ_BITS'b1000_10_1111; // JLI_BASE

parameter FSM_EPIL_S3      =     `npuarc_UOP_SIRQ_BITS'b1010_00_1000; // AEX
parameter FSM_EPIL_S4      =     `npuarc_UOP_SIRQ_BITS'b1010_10_0010; // BLINK
parameter FSM_EPIL_S6      =     `npuarc_UOP_SIRQ_BITS'b1010_10_0011; // R30
parameter FSM_EPIL_S7      =     `npuarc_UOP_SIRQ_BITS'b1010_11_0000; // GPR
parameter FSM_EPIL_S8      =     `npuarc_UOP_SIRQ_BITS'b1010_10_0001; // PCL
parameter FSM_EPIL_S9      =     `npuarc_UOP_SIRQ_BITS'b1010_10_0000; // STAT32
parameter FSM_EPIL_S10     =     `npuarc_UOP_SIRQ_BITS'b1010_00_1010; // SP
parameter FSM_EPIL_S11     =     `npuarc_UOP_SIRQ_BITS'b1010_00_1001; // AEX
parameter FSM_EPIL_S12     =     `npuarc_UOP_SIRQ_BITS'b1111_00_1011; // J ilink
parameter FSM_EPIL_S13     =     `npuarc_UOP_SIRQ_BITS'b1010_10_0110; // LP_END
parameter FSM_EPIL_S14     =     `npuarc_UOP_SIRQ_BITS'b1010_10_0101; // LP_START
parameter FSM_EPIL_S15     =     `npuarc_UOP_SIRQ_BITS'b1010_10_0100; // LP_COUNT
parameter FSM_EPIL_S16     =     `npuarc_UOP_SIRQ_BITS'b1010_10_1001; // EI_BASE
parameter FSM_EPIL_S17     =     `npuarc_UOP_SIRQ_BITS'b1010_10_1000; // LDI_BASE
parameter FSM_EPIL_S18     =     `npuarc_UOP_SIRQ_BITS'b1010_10_0111; // JLI_BASE
parameter FSM_EPIL_S19     =     `npuarc_UOP_SIRQ_BITS'b1010_10_1111; // JLI_BASE
parameter FSM_EPIL_S20     =     `npuarc_UOP_SIRQ_BITS'b1010_10_1100; // LP_COUNT

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @fsm_irq_control_PROC                                                    //
//                                                                          //
// Process to calculate any ancillary state used when determine the         //
// next-state of the 'sirq' state machine.                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: fsm_irq_control_PROC

  //==========================================================================
  // Control state indicating that the machine will transition back to
  // user-mode upon the completion of the current epilogue sequence.
  // A special case needs to be taken care when we replay the epilogue sequence
  // due to wa_replay_r
  //
  irq_rtrn_to_u     = ar_aux_irq_act_r[`npuarc_IRQ_ACT_U_BIT]
                    & (    ca_irq_act_nxt[`npuarc_IRQ_ACT_ACT_RANGE]
                        == `npuarc_NUMBER_OF_LEVELS'b0
                      )
                    ;



  //==========================================================================
  // 'irq_gpr_max' is calculated as the final (inclusive) GPR to be
  // pushed to/popped from the stack as a function of the current
  // value of IRQ_CTRL_AUX.
  //
//leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator
// LJ:  subtraction of 1 is intentional
//leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ: ignore warnings about loss of carry from this addition  
//leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  subtraction of 1 is intentional
  irq_gpr_max       = {  1'd0
                        , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_NR_RANGE]
                        , 1'b0
                       }
                    - `npuarc_UOP_CNT_BITS'd1 
                    - da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_GPR] 
                    ;

//modification of the max register number in case of 16 RGF_NUM_REGS
//
//leda B_3200 on
//leda BTTF_D002 on
//leda W484 on
  //==========================================================================
  // Asserted when there is a non-zero number of gpr registers to be
  // pushed to/popped from the stack.
  //
  irq_gpr_nz        = (|ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_NR_RANGE])
                    ;

  //==========================================================================
  // The GPR count has yet to be exhausted.
  //
  irq_dstreg_ne     = (da_uop_dstreg_r != irq_gpr_max)
                    ;

  //==========================================================================
  //
  //
  irq_doblink       = ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_B_BIT]
                    & (    ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_NR_RANGE]
                        != `npuarc_IRQ_CTRL_NR_BITS'd16
                      )
                    ;

end // block: fsm_irq_control_PROC





//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @da_uop_sirq_nxt_PROC                                                    //
//                                                                          //
// Process to calculate the next-state update to the 'sirq'                 //
// state-machine.                                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire da_uop_sirq_busy_case;
assign da_uop_sirq_busy_case = da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_BUSY] | sirq_prol | sirq_epil;

wire int_nopp_force_case;
assign int_nopp_force_case = wa_restart_cmd_r[`npuarc_RSRT_IS_IRQ_CHAIN];

wire [6:0] sirq_prol_case;
assign sirq_prol_case = { 
                     1'b0
                   , (   ~ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_U_BIT]
                       &  ar_aux_status32_r[`npuarc_U_FLAG])
                   , irq_doblink
                   , irq_gpr_nz
                   , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
                   , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
                   , wa_restart_cmd_r[`npuarc_RSRT_IS_IRQ_CHAIN]
                 };

wire [3:0] sirq_prol_s1_case;
assign sirq_prol_s1_case = {
                 irq_doblink
               , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
               , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
               , irq_gpr_nz
             };

wire [1:0] sirq_prol_s4_case;
assign sirq_prol_s4_case = {   
                  ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
                , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
             };

wire [3:0] sirq_prol_s7_case;
assign sirq_prol_s7_case = {  
                irq_doblink
              , irq_dstreg_ne
              , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
              , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
             };

wire [5:0] sirq_epil_case;
assign sirq_epil_case = { 
                     1'b0
                   , (   ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_U_BIT]
                       & irq_rtrn_to_u
                       & (!int_rtie_replay_r)
                     )
                   , irq_gpr_nz
                   , irq_doblink
                   , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
                   , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
                 };

wire [3:0] sirq_epil_s3_case;
assign sirq_epil_s3_case = {
                 irq_gpr_nz
               , irq_doblink
               , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
               , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
             };

wire [1:0] sirq_epil_s4_case;
assign sirq_epil_s4_case = {
                   ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
                 , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
             };

wire [3:0] sirq_epil_s7_case;
assign sirq_epil_s7_case = {
                 irq_dstreg_ne
               , irq_doblink
               , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
               , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
             };

always @*
begin: da_uop_sirq_nxt_PROC

  //==========================================================================
  // Assign defaults
  //
  da_uop_sirq_nxt       = FSM_SIRQ_S0;
  sirq_prol_retain      = 1'b0;

  //==========================================================================
  // Interrupt FSM next-state logic
  //
  case (da_uop_sirq_r)

    FSM_SIRQ_S0:
      // emit: n/a
      case (1'b1)
        sirq_prol: begin
          casez (sirq_prol_case)
            7'b0_?????1: da_uop_sirq_nxt = FSM_PROL_S10;
            7'b0_1????0: da_uop_sirq_nxt = FSM_PROL_S1;
            7'b0_0?1??0: da_uop_sirq_nxt = FSM_PROL_S7;
            7'b0_010??0: da_uop_sirq_nxt = FSM_PROL_S4;
            7'b0_0001?0: da_uop_sirq_nxt = FSM_PROL_S13;
            7'b0_000010: da_uop_sirq_nxt = FSM_PROL_S16;
            7'b0_000000: da_uop_sirq_nxt = FSM_PROL_S3; 
            default:     da_uop_sirq_nxt = FSM_SIRQ_S0; 
          endcase
        end

        sirq_epil: begin
          casez (sirq_epil_case)
            6'b0_1????: da_uop_sirq_nxt = FSM_EPIL_S3;
            6'b0_01???: da_uop_sirq_nxt = FSM_EPIL_S7;
            6'b0_001??: da_uop_sirq_nxt = FSM_EPIL_S4;
            6'b0_0001?: da_uop_sirq_nxt = FSM_EPIL_S13;
            6'b0_00001: da_uop_sirq_nxt = FSM_EPIL_S16;
            6'b0_00000: da_uop_sirq_nxt = FSM_EPIL_S8;
            default:    da_uop_sirq_nxt = FSM_SIRQ_S0;
          endcase // casez ( {   fsm_op_nxt...

        end
      default: ;
      endcase // case (1'b1)


    FSM_EPIL_S3:
      // emit: aex sp, [AUX_USER_SP]
      casez (sirq_epil_s3_case)
        4'b1???: da_uop_sirq_nxt = FSM_EPIL_S7;
        4'b01??: da_uop_sirq_nxt = FSM_EPIL_S4;
        4'b001?: da_uop_sirq_nxt = FSM_EPIL_S13;
        4'b0001: da_uop_sirq_nxt = FSM_EPIL_S16;
        default: da_uop_sirq_nxt = FSM_EPIL_S8;
      endcase

    FSM_EPIL_S7:
      // emit: pop (gpr[X])
      casez (sirq_epil_s7_case)
        4'b1???: da_uop_sirq_nxt = FSM_EPIL_S7;
        4'b01??: da_uop_sirq_nxt = FSM_EPIL_S4;
        4'b001?: da_uop_sirq_nxt = FSM_EPIL_S13;
        4'b0001: da_uop_sirq_nxt = FSM_EPIL_S16;
        default: da_uop_sirq_nxt = FSM_EPIL_S8;
      endcase

    FSM_EPIL_S4:
      // emit: pop (gpr[blink])
      casez (sirq_epil_s4_case)
        2'b1?:   da_uop_sirq_nxt = FSM_EPIL_S13;
        2'b01:   da_uop_sirq_nxt = FSM_EPIL_S16;
        default: da_uop_sirq_nxt = FSM_EPIL_S8;
      endcase

    FSM_EPIL_S13:
      // emit: pop (aux[lp_end])
      da_uop_sirq_nxt = FSM_EPIL_S14;

    FSM_EPIL_S14:
      // emit: pop (aux[lp_start])
      da_uop_sirq_nxt = FSM_EPIL_S15;

    FSM_EPIL_S15:
      // emit: pop (aux[lp_count])
      da_uop_sirq_nxt =
                      (ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT] == 1'b1)
                    ? FSM_EPIL_S16 :
                      FSM_EPIL_S8
                    ;

    FSM_EPIL_S16:
      // emit: pop (aux[ei_base])
      da_uop_sirq_nxt = FSM_EPIL_S17;

    FSM_EPIL_S17:
      // emit: pop (aux[ldi_base])
      da_uop_sirq_nxt = FSM_EPIL_S18;

    FSM_EPIL_S18:
      // emit: pop (aux[jli_base])
      da_uop_sirq_nxt = FSM_EPIL_S8;

    FSM_EPIL_S8:
      // emit: pop (gpr[pcl])
      da_uop_sirq_nxt = FSM_EPIL_S9;

    FSM_EPIL_S9:
      // emit: pop (aux[status32])
      da_uop_sirq_nxt = FSM_EPIL_S10;

    FSM_EPIL_S10:
      // emit: sub sp, sp, offset
      da_uop_sirq_nxt = (   ~ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_U_BIT]
                        &  irq_rtrn_to_u
                      )
                    ? FSM_EPIL_S11
                    : FSM_EPIL_S12
                    ;

    FSM_EPIL_S11:
      // emit: aex sp, [AUX_USER_SP]
      da_uop_sirq_nxt = FSM_EPIL_S12;

    FSM_EPIL_S12:
      // emit: j [ilink]
      da_uop_sirq_nxt = FSM_SIRQ_S0;

    FSM_PROL_S1:
      // emit: aex sp, [AUX_USER_SP]
      casez (sirq_prol_s1_case)
        4'b???1: da_uop_sirq_nxt = FSM_PROL_S7;
        4'b1??0: da_uop_sirq_nxt = FSM_PROL_S4;
        4'b0?10: da_uop_sirq_nxt = FSM_PROL_S13;
        4'b0100: da_uop_sirq_nxt = FSM_PROL_S16;
        default: da_uop_sirq_nxt = FSM_PROL_S3;
      endcase

    FSM_PROL_S2:
      // emit: push (aux[status32])
      da_uop_sirq_nxt = FSM_PROL_S8;

    FSM_PROL_S3:
      // emit: push (gpr[pc])
      da_uop_sirq_nxt = FSM_PROL_S2;

    FSM_PROL_S14:
      // emit: push (aux[jli_base])
      da_uop_sirq_nxt = FSM_PROL_S3;

    FSM_PROL_S15:
      // emit: push (aux[ldi_base])
       da_uop_sirq_nxt = FSM_PROL_S14;

    FSM_PROL_S16:
      // emit: push (aux[ei_base])
      da_uop_sirq_nxt = FSM_PROL_S15;

    FSM_PROL_S11:
      // emit: push (aux[lp_count])
      da_uop_sirq_nxt =
                      (ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT] == 1'b1)
                    ? FSM_PROL_S16 :
                      FSM_PROL_S3
                    ;

    FSM_PROL_S12:
      // emit: push (aux[lp_start])
      da_uop_sirq_nxt = FSM_PROL_S11;

    FSM_PROL_S13:
      // emit: push (aux[lp_end])
      da_uop_sirq_nxt = FSM_PROL_S12;

    FSM_PROL_S4:
      // emit: push (gpr[blink])
      casez (sirq_prol_s4_case)
        2'b1?:   da_uop_sirq_nxt = FSM_PROL_S13;
        2'b01:   da_uop_sirq_nxt = FSM_PROL_S16;
        default: da_uop_sirq_nxt = FSM_PROL_S3;
      endcase

    FSM_PROL_S7:
      // emit: push (gpr[X])
      casez (sirq_prol_s7_case)
        4'b?1??: da_uop_sirq_nxt = FSM_PROL_S7;
        4'b10??: da_uop_sirq_nxt = FSM_PROL_S4;
        4'b001?: da_uop_sirq_nxt = FSM_PROL_S13;
        4'b0001: da_uop_sirq_nxt = FSM_PROL_S16;
        default: da_uop_sirq_nxt = FSM_PROL_S3;
      endcase

    FSM_PROL_S8:
      // emit: add sp, sp, offset
      da_uop_sirq_nxt = (   ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_U_BIT]
                        & ar_aux_status32_r[`npuarc_U_FLAG])
                    ? FSM_PROL_S9
                    : FSM_PROL_S10
                    ;

    FSM_PROL_S9:
      // emit: aex sp, [AUX_USER_SP]
      da_uop_sirq_nxt = FSM_PROL_S10;

    FSM_PROL_S10:
      // emit: J vector
      da_uop_sirq_nxt = FSM_SIRQ_S0;
    default: ;
  endcase // casez ( { fsm_op_r, da_uop_sirq_r } )

  //==========================================================================
  // We allow restart in case there is an exception during sirq sequence
  // In case the restart happens on prologue instructions (for store) 
  //   the corresponding interrupt will not be acked and the
  //   killed sequence will eventually be restarted by the pending interrupt
  // In case the restart happens on epilogure instructions (for load)
  //   the corresponding epilogue sequence needs to be completed after the exception
  //   by a replay of rtie instrction
  if (excpn_prol) begin
    da_uop_sirq_nxt   = FSM_SIRQ_S0;
  end
  // for int_nopp case, epilogue is sepculative before nopp is commited
  // we need to jump to NOPP state if noop event is commtted
  // 
  else if (int_nopp_force_case) begin
    da_uop_sirq_nxt   = FSM_PROL_S10; 
  end
  // State-transition override on restart
  //  do not kill irq restart itself
  // We allow restart in case it's speculative epilogue
  //  and we also need to retain the restart command 'sirq_prol' 
  //  as is a single pulse. the retained signal sirq_prol_retain will be
  //  used to re-start a new prologue sequence
  //
  else if (da_kill) begin 
    da_uop_sirq_nxt   = FSM_SIRQ_S0;
    sirq_prol_retain  = sirq_prol;
  end

end // block: uop_irq_nxt_PROC



parameter FSM_FIRQ_S0        =   5'b000_00;

parameter FSM_FIRQ_EXCPNP_S1 =   5'b100_10;
parameter FSM_FIRQ_EXCPNP_S2 =   5'b101_11;

parameter FSM_FIRQ_EXCPNE_S1 =   5'b110_10;
parameter FSM_FIRQ_EXCPNE_S2 =   5'b111_11;



parameter FSM_ENTER_S0     =     `npuarc_UOP_SIRQ_BITS'b0000_00_0000; // IDLE

parameter FSM_ENTER_S1     =     `npuarc_UOP_SIRQ_BITS'b1000_10_0010; // BLINK
parameter FSM_ENTER_S7     =     `npuarc_UOP_SIRQ_BITS'b1000_11_0000; // GPR
parameter FSM_ENTER_S3     =     `npuarc_UOP_SIRQ_BITS'b1000_10_1100; // FP
parameter FSM_ENTER_S4_X0  =     `npuarc_UOP_SIRQ_BITS'b1000_00_1010; // SP
parameter FSM_ENTER_S4_X1  =     `npuarc_UOP_SIRQ_BITS'b1001_00_1010; // SP
parameter FSM_ENTER_S4     =     `npuarc_UOP_SIRQ_BITS'b1000_00_1010; // SP
parameter FSM_ENTER_S40    =     `npuarc_UOP_SIRQ_BITS'b1000_00_1010; // SP
parameter FSM_ENTER_S5     =     `npuarc_UOP_SIRQ_BITS'b1001_00_1100; // FP

parameter FSM_LEAVE_S1     =     `npuarc_UOP_SIRQ_BITS'b1010_00_1100; // SP
parameter FSM_LEAVE_S2     =     `npuarc_UOP_SIRQ_BITS'b1010_10_0010; // BLINK
parameter FSM_LEAVE_S4     =     `npuarc_UOP_SIRQ_BITS'b1010_10_1100; // FP
parameter FSM_LEAVE_S5     =     `npuarc_UOP_SIRQ_BITS'b1110_00_1101; // J.d
parameter FSM_LEAVE_S6     =     `npuarc_UOP_SIRQ_BITS'b1011_00_1010; // ADD
parameter FSM_LEAVE_S7     =     `npuarc_UOP_SIRQ_BITS'b1010_11_0000; // GPR



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @fsm_enter_control_PROC                                                  //
//                                                                          //
// Process to calculate ancilliary state used when derive the next          //
// state in the 'enter' fsm.                                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: fsm_enter_control_PROC

  //==========================================================================
  // Derived the supremum of the GPR set to save to/restore from the
  // stack.
  //
// leda B_3208 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in srithmetic assignment 
// LJ:  address arithmetic (dont_care carry bit)
  {dont_care_0, enter_dstreg_max} = da_uop_enter_u7_r[`npuarc_OPD_REG_RANGE] + 12;
///                     + `UOP_CNT_BITS'd12
///                     ;
// leda B_3200 on
// leda B_3208 on
  //==========================================================================
  // dstreg is not-equal to max(dstreg) as a function of the initial
  // operand.
  //
  enter_dstreg_ne   = (   (da_uop_dstreg_r != enter_dstreg_max)
                        & (~al_uop_do_pair)
                      )
                    | (   al_uop_do_pair
                        & (    da_uop_dstreg_r
                            != {   enter_dstreg_max[`npuarc_UOP_CNT_MSB:1]
                                 , 1'b0
                               }
                          )
                      )
                    ;

end // block: fsm_enter_nxt_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @do_pair_PROC                                                          //
//                                                                        //
// Process to compute whether the current GPR op. should be promoted      //
// to a LDD/STD instruction. Arguably, this logic should reside in the    //
// DA stage as it is derived as a function of the DA-state however it     //
// is included here because the calculate also makes use of some          //
// additional state that should not be exposed globally.                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                 gpr_is_final;
reg                 gpr_is_odd;

always @*
begin: do_pair_PROC

  //==========================================================================
  // Do not promote if GPR is even and the final GPR to be pushed/popped.
  //
  dstreg_max        = (enter_dstreg_max & {`npuarc_UOP_CNT_BITS{da_uop_enter_r[`npuarc_UOP_ENTER_IS_BUSY]}})
                    | (irq_gpr_max      & {`npuarc_UOP_CNT_BITS{da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_BUSY]}})
                    ;
  gpr_is_final      = (da_uop_dstreg_r == dstreg_max)
                    ;

  //==========================================================================
  // Do not promote if base GPR is odd (an architectural requirement).
  //
  gpr_is_odd        = da_uop_dstreg_r[0]
                    ;

  //==========================================================================
  //
  al_uop_do_pair    =  ( da_uop_enter_r[`npuarc_UOP_ENTER_IS_GPR] 
                       & (~(   gpr_is_final
                            | gpr_is_odd
                          ))
                       )
                       | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_GPR]
                       ;
end // block: do_pair_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @da_uop_enter_nxt_PROC                                                   //
//                                                                          //
// Process to calculate the next-state update to the 'enter' FSM.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_UOP_SIRQ_RANGE]         enter_s4_is_term;

always @*
begin: da_uop_enter_nxt_PROC

  //==========================================================================
  // A mask is derived to OR with the FSM_ENTER_S4 state as the
  // terminal nature of the state is conditional on the FP of the
  // instruction operand. The state-encoding of FSM_ENTER_S4_X contains
  // a don't-care entry where the IS_TERM would otherwise reside to
  // allow one entry to handle both cases.
  //
  enter_s4_is_term  = (da_uop_enter_u7_r[`npuarc_OPD_FP_BIT] == 1'b1)
                    ? `npuarc_UOP_SIRQ_BITS'd0
                    : `npuarc_UOP_SIRQ_BITS'd64
                    ;

  //==========================================================================
  // Assign defaults
  //
  da_uop_enter_nxt   = da_uop_enter_r;

  //==========================================================================
  // ENTER_S/LEAVE_S-state transition logic.
  //
  case (da_uop_enter_r)

    FSM_ENTER_S0:
      // emit: n/a
    begin
  // leda W226 off
  // LMD: Case select expression is constant
  // LJ:  A constant select expression is required in this case
  // leda W225 off
  // LMD: Case item expression is not constant
  // LJ:  A non-constant case-itme expression is required in this case
  //   
      case (1'b1)
        (   al_uop_is_enter
          & al_enter_op):
        begin
          casez ({   da_uop_enter_u7_nxt[`npuarc_OPD_LINK_BIT]
                   , (|da_uop_enter_u7_nxt[`npuarc_OPD_REG_RANGE])
                   , da_uop_enter_u7_nxt[`npuarc_OPD_FP_BIT]
                 })
            3'b1??: da_uop_enter_nxt  = FSM_ENTER_S1;
            3'b01?: da_uop_enter_nxt  = FSM_ENTER_S7;
            3'b001: da_uop_enter_nxt  = FSM_ENTER_S3;
            default: ;
          endcase // casez ( {   fsm_op_nxt...
        end

        (    al_uop_is_enter
          & (~al_enter_op)):
        begin
          casez ({   da_uop_enter_u7_nxt[`npuarc_OPD_FP_BIT]
                   , da_uop_enter_u7_nxt[`npuarc_OPD_LINK_BIT]
                   , (|da_uop_enter_u7_nxt[`npuarc_OPD_REG_RANGE])
                   , da_uop_enter_u7_nxt[`npuarc_OPD_BLINK_BIT]
                 })
            4'b1???: da_uop_enter_nxt = FSM_LEAVE_S1;
            4'b01??: da_uop_enter_nxt = FSM_LEAVE_S2;
            4'b001?: da_uop_enter_nxt = FSM_LEAVE_S7;
            4'b0001: da_uop_enter_nxt = FSM_LEAVE_S5;
            default: da_uop_enter_nxt = FSM_ENTER_S0;
          endcase // casez ( {   da_uop_enter_u7_nxt[`OPD_FP_BIT]...
        end
        default: ;
      endcase // case (1'b1)
   // leda W226 on
  // leda W225 on     
    end // FSM_ENTER_S0

    FSM_ENTER_S1:
    begin
      // emit: push (blink)
      casez ({   (|da_uop_enter_u7_r[`npuarc_OPD_REG_RANGE])
               , da_uop_enter_u7_r[`npuarc_OPD_FP_BIT]
             })
        2'b1?:   da_uop_enter_nxt = FSM_ENTER_S7;
        2'b01:   da_uop_enter_nxt = FSM_ENTER_S3;
        default: da_uop_enter_nxt = (   FSM_ENTER_S40
                                     | enter_s4_is_term
                                   )
                                 ;
      endcase
    end // FSM_ENTER_S1

    FSM_ENTER_S7:
      // emit: push (r[])
    begin
      casez ({   enter_dstreg_ne
               , da_uop_enter_u7_r[`npuarc_OPD_FP_BIT]
             })
        2'b1?:   da_uop_enter_nxt = FSM_ENTER_S7;
        2'b01:   da_uop_enter_nxt = FSM_ENTER_S3;
        default: da_uop_enter_nxt = (   FSM_ENTER_S40
                                      | enter_s4_is_term
                                   )
                                 ;
      endcase
    end // FSM_ENTER_S7

    FSM_ENTER_S3:
      // emit: push (fp)
      da_uop_enter_nxt = (   FSM_ENTER_S40
                           | enter_s4_is_term
                        )
                      ;

    FSM_ENTER_S4_X0,
    FSM_ENTER_S4_X1:
      // emit: sub sp, sp, offset
      da_uop_enter_nxt = (da_uop_enter_u7_r[`npuarc_OPD_FP_BIT] == 1'b1)
                      ? FSM_ENTER_S5
                      : FSM_ENTER_S0
                      ;

    FSM_ENTER_S5:
      // emit: mov fp, sp
      da_uop_enter_nxt = FSM_ENTER_S0;

    FSM_LEAVE_S1:
      // emit: mov sp, fp
      casez ({   da_uop_enter_u7_r[`npuarc_OPD_LINK_BIT]
               , (|da_uop_enter_u7_r[`npuarc_OPD_REG_RANGE])
             })
        2'b1?:   da_uop_enter_nxt = FSM_LEAVE_S2;
        2'b01:   da_uop_enter_nxt = FSM_LEAVE_S7;
        default: da_uop_enter_nxt = FSM_LEAVE_S4;
      endcase

    FSM_LEAVE_S2:
      // emit: pop (blink)
      casez ({   da_uop_enter_u7_r[`npuarc_OPD_FP_BIT]
               , (|da_uop_enter_u7_r[`npuarc_OPD_REG_RANGE])
               , da_uop_enter_u7_r[`npuarc_OPD_BLINK_BIT]
             })
        3'b?1?:  da_uop_enter_nxt = FSM_LEAVE_S7;
        3'b10?:  da_uop_enter_nxt = FSM_LEAVE_S4;
        3'b001:  da_uop_enter_nxt = FSM_LEAVE_S5;
        default: da_uop_enter_nxt = FSM_LEAVE_S6;
      endcase

    FSM_LEAVE_S7:
      // emit: push (r[])
      casez ({   da_uop_enter_u7_r[`npuarc_OPD_FP_BIT]
               , enter_dstreg_ne
               , da_uop_enter_u7_r[`npuarc_OPD_BLINK_BIT]
             })
        3'b?1?:  da_uop_enter_nxt = FSM_LEAVE_S7;
        3'b10?:  da_uop_enter_nxt = FSM_LEAVE_S4;
        3'b001:  da_uop_enter_nxt = FSM_LEAVE_S5;
        default: da_uop_enter_nxt = FSM_LEAVE_S6;
      endcase

    FSM_LEAVE_S4:
      // emit: pop (fp)
      da_uop_enter_nxt = (da_uop_enter_u7_r[`npuarc_OPD_BLINK_BIT] == 1'b1)
                       ? FSM_LEAVE_S5
                       : FSM_LEAVE_S6
                       ;

    FSM_LEAVE_S5:
      // emit: J.D [blink]
      da_uop_enter_nxt = FSM_LEAVE_S6;

    FSM_LEAVE_S6:
      // emit: add sp, sp, offset
      da_uop_enter_nxt = FSM_ENTER_S0;
    default: ;
  endcase // casez (da_uop_enter_r)

  //==========================================================================
  // State-transition override on restart
  //
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  overwriting default assignment
  if (da_kill == 1'b1)
    da_uop_enter_nxt = FSM_ENTER_S0;
// spyglass enable_block W415a
end // block: da_uop_enter_nxt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @dstreg_PROC                                                             //
//                                                                          //
// Process to derive the next-state update to the 'dstreg' counter,         //
// used to maintain the index of GPR to be pushed to/popped from the        //
// stack.                                                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_UOP_CNT_RANGE]        dstreg_init;
reg [`npuarc_UOP_CNT_RANGE]        dstreg_delta;
reg [`npuarc_UOP_CNT_RANGE]        dstreg_delta_tmp;

always @*
begin: dstreg_PROC

  //==========================================================================
  // Derive the initial value for the 'dstreg' counter. The only time
  // it is initialised to a non-zero value is when initiating either a
  // ENTER_S or LEAVE_S instruction.
  //
  dstreg_init       = (al_inst_is_enter == 1'b1)
                    ? `npuarc_UOP_CNT_BITS'd13
                    : `npuarc_UOP_CNT_BITS'd0
                    ;

  //==========================================================================
  // Derive the dstreg delta to be added to the counter after each
  // push/pop operation.
  //
  dstreg_delta_tmp  = (al_uop_do_pair == 1'b1)
                    ? `npuarc_UOP_CNT_BITS'd2
                    : `npuarc_UOP_CNT_BITS'd1
                    ;

  dstreg_delta = dstreg_delta_tmp;


  //==========================================================================
  // Derive the next value of the 'dstreg' counter.
  //
// spyglass disable_block W484
// leda B_3208_A off  
// LMD: Unequal length  operand in conditional expression, false_alt: 8, true_alt : 7
// leda B_3200 off
// LMD: Unequal length LHS and RHS in srithmetic assignment 
// LJ:  address arithmetic (dont_care carry bit)
// LJ:  true value may have carry bit and should be considered 8 bit long
  {dont_care_1, da_uop_dstreg_nxt} = (da_uop_busy_r == 1'b1) & (~wa_restart_r)
                    ? (da_uop_dstreg_r + dstreg_delta)
                    : {1'b0, dstreg_init}
                    ;
// leda B_3200 on
// leda B_3208_A on
// spyglass enable_block W484               
end // block: dstreg_PROC



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @sirq_sp_init_nxt_PROC                                                   //
//                                                                          //
// Process to implement the data-path which derived the initial             //
// stack-pointer offset for 'sirq' operations as non-trivial function       //
// of the AUX_IRQ_CTRL register.                                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_UOP_CNT_RANGE]          sirq_sp_suma;
reg [`npuarc_UOP_CNT_RANGE]          sirq_sp_sumb;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Used in case expression
reg [2:0]                     sirq_sp_cntrl;
// leda NTL_CON13A on
always @*
begin: sirq_sp_init_nxt_PROC

  //==========================================================================
  // Derivation of stack-pointer offset for aux. registers.
  //
  sirq_sp_suma   = `npuarc_UOP_CNT_BITS'd0;
  case ({   irq_doblink
          , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_L_BIT]
          , ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_LP_BIT]
        })
    3'd0:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd2;
    3'd1:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd5;
    3'd2:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd5;
    3'd3:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd8;
    3'd4:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd3;
    3'd5:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd6;
    3'd6:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd6;
    3'd7:
      sirq_sp_suma       = `npuarc_UOP_CNT_BITS'd9;
 default: ;
  endcase

  //==========================================================================
  // Derivation of stack-pointer offset for GPR registers.
  //
  sirq_sp_sumb           = {
                               1'd0,
                               ar_aux_irq_ctrl_r[`npuarc_IRQ_CTRL_NR_RANGE]
                             , 1'b0
                           }
                         ;

  //==========================================================================
  // The interrupt prologue stack-pointer offset is calculated in
  // three-steps:
  //
  //  spoff_cntrl[0]: load the result register with condsum.
  //  spoff_cntrl[1]: add ar_aux_irq_ctrl_r.nr to the result.
  //  spoff_cntrl[2]: negate result.
  //
  // The value contained in the result register is the derived
  // stack-pointer offset as a function of AR_AUX_IRQ_CTRL_R. During
  // the calculation steps, the uop_seq will stall any incoming
  // interrupt prologue requests until they have completed.
  //
  sirq_sp_cntrl          = {   sirq_sp_cntrl_r
                             , ar_aux_irq_ctrl_upt_r
                           }
                         ;

  //==========================================================================
  // The sirq_sp control state is implemented as a simple shift
  // register.
  //
  sirq_sp_cntrl_nxt      = sirq_sp_cntrl[1:0]
                         ;

  //==========================================================================
  // Derive the REG update data path as a function of the current
  // controller state. Notably, derive the datapath state as a
  // priority decoder to ensure that the machine is suitably restarted
  // when back-to-back SR to AUX_IRQ_CTRL take place before the
  // initial condition has completed.
  //
  //
  casez (sirq_sp_cntrl)
// spyglass disable_block W484, W164a
//leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ: ignore warnings about loss of carry from this addition  
//leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator
//leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  addition/subtraction of less bits than result is intentional
    3'b??1: da_uop_sirq_spi_nxt = sirq_sp_suma
                                ;
    3'b?10: da_uop_sirq_spi_nxt = sirq_sp_sumb
                                + da_uop_sirq_spi_r
                                ;
    3'b100: da_uop_sirq_spi_nxt = `npuarc_UOP_CNT_BITS'd0
                                - da_uop_sirq_spi_r
                                ;
    default:da_uop_sirq_spi_nxt = `npuarc_UOP_CNT_BITS'd0
                                ;
//leda W484 on
//leda B_3200 on                                ;
//leda BTTF_D002 on
// spyglass enable_block W484, W164a
  endcase // casez (sirq_sp_cntrl)

  //==========================================================================
  // Initialise the interrupt stack-pointer initialisation whenever
  // the controller has completed a new calculation (originally
  // initiated by a write to AUX_IRQ_CTRL).
  //
  al_uop_sirq_haz        = (|sirq_sp_cntrl)
                         | irq_ctrl_wen
                         ;

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @da_uop_enter_spi_nxt_PROC                                               //
//                                                                          //
// Process to derive the initial stack-pointer offset for ENTER-class       //
// instructions as a function of the u7 immediate operand.                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: da_uop_enter_spi_nxt_PROC

  // Process to calculate the initial stack-pointer offset as a function
  // of the u7 of ENTER_S instructions.
  //

  //==========================================================================
  // Assign defaults
  //
  da_uop_enter_spi_nxt   = `npuarc_UOP_CNT_BITS'd0;

  //==========================================================================
  // 'Fast'-lookup table to the ENTER_S stack-pointer offset:
  //
  // uop_da_uop_enter_spi = -(u7[reg] + u7[link] + u7[fp])
  //
  case ({   da_uop_enter_u7_nxt[`npuarc_OPD_REG_RANGE]
          , (   da_uop_enter_u7_nxt[`npuarc_OPD_FP_BIT]
              & da_uop_enter_u7_nxt[`npuarc_OPD_LINK_BIT]
            )
          , (   da_uop_enter_u7_nxt[`npuarc_OPD_FP_BIT]
              ^ da_uop_enter_u7_nxt[`npuarc_OPD_LINK_BIT]
            )
        })
    {4'd0, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd0;
    {4'd0, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd127;
    {4'd0, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd126;
    {4'd1, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd127;
    {4'd1, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd126;
    {4'd1, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd125;
    {4'd2, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd126;
    {4'd2, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd125;
    {4'd2, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd124;
    {4'd3, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd125;
    {4'd3, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd124;
    {4'd3, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd123;
    {4'd4, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd124;
    {4'd4, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd123;
    {4'd4, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd122;
    {4'd5, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd123;
    {4'd5, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd122;
    {4'd5, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd121;
    {4'd6, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd122;
    {4'd6, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd121;
    {4'd6, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd120;
    {4'd7, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd121;
    {4'd7, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd120;
    {4'd7, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd119;
    {4'd8, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd120;
    {4'd8, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd119;
    {4'd8, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd118;
    {4'd9, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd119;
    {4'd9, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd118;
    {4'd9, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd117;
    {4'd10, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd118;
    {4'd10, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd117;
    {4'd10, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd116;
    {4'd11, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd117;
    {4'd11, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd116;
    {4'd11, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd115;
    {4'd12, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd116;
    {4'd12, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd115;
    {4'd12, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd114;
    {4'd13, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd115;
    {4'd13, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd114;
    {4'd13, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd113;
    {4'd14, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd114;
    {4'd14, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd113;
    {4'd14, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd112;
    {4'd15, 2'd0}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd113;
    {4'd15, 2'd1}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd112;
    {4'd15, 2'd2}:
      da_uop_enter_spi_nxt = `npuarc_UOP_CNT_BITS'd111;
  default: ;
  endcase // case ( {   da_uop_enter_u7_nxt[`OPD_FP_BIT]...

end // block: da_uop_enter_spi_nxt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @spoff_PROC                                                              //
//                                                                          //
// Process to derive the state update to the stack-pointer offset as a      //
// function of the current machine state and the instruction currently      //
// being emitted.                                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                         spoff_inc;
reg [`npuarc_UOP_CNT_RANGE]        spoff_delta;
reg [`npuarc_UOP_CNT_RANGE]        spoff_fast;

always @*
begin: spoff_PROC

  //==========================================================================
  // Increment the stack-offset pointer whenever the instruction
  // emitted references the stack and the FSM is progressing to the
  // next state.
  //
  spoff_inc         = 1'b0
                    | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_MEM]
                    | (da_uop_enter_r[`npuarc_UOP_ENTER_IS_MEM] & (~wa_restart_r))
                    ;

  //==========================================================================
  // Derive the spoff delta to be added to the counter after each
  // push/pop operation.
  spoff_delta       = (al_uop_do_pair == 1'b1)
                    ? `npuarc_UOP_CNT_BITS'd2
                    : `npuarc_UOP_CNT_BITS'd1
                    ;

  //==========================================================================
  // Determine next value of the stack-pointer offset counter.
  //
  casez ({   sirq_prol
           , al_inst_is_rtie
           , ar_aux_status32_r[`npuarc_AE_FLAG]
           ,   1'b0
         })
    4'b1??_?: spoff_fast = da_uop_sirq_spi_r;
    4'b010_0: spoff_fast = `npuarc_UOP_CNT_BITS'd0;
    default:  spoff_fast = da_uop_spoff_r;
  endcase // casez ({   uop_irqprol...


  //==========================================================================
  // The decoding of the ENTER/LEAVE-state is slightly more complex
  // due to the presence of the u7 operand which determines the
  // stack-pointer offset, therefore multiplex the values towards the
  // end of the spoff_nxt logic-cone.
  //
  casez ({   spoff_inc
           , al_inst_is_enter
           , al_enter_op
         })
// spyglass disable_block W484, W164a
// SMD: possible loss of carry/borrow due to addition/subtraction
// SJ:  addition of less bits is intentional
//leda W484 off
// LMD:Possible loss of carry/borrow in addition/subtraction LHS : 7, RHS : 8
//leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  addition of less bits is intentional
    3'b1_??: da_uop_spoff_nxt  = (da_uop_spoff_r + spoff_delta);
//leda BTTF_D002 on
//leda W484 on
// spyglass enable_block W484, W164a
    3'b0_10: da_uop_spoff_nxt  = `npuarc_UOP_CNT_BITS'b0;
    3'b0_11: da_uop_spoff_nxt  = da_uop_enter_spi_nxt;
    default: da_uop_spoff_nxt  = spoff_fast;
  endcase // casez ({   uop_al_is_enter...


end // block: uop_spoff_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @decode_PROC                                                             //
//                                                                          //
// Process to decode the aligned instruction in AL and identify             //
// whether the instruction is either a epilogue initating RTIE              //
// instruction or a ENTER_S/LEAVE_S.                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: decode_PROC

  //==========================================================================
  // u7 field of ENTER_S/LEAVE_S where applicable.
  //
  da_uop_enter_u7_nxt    = {   al_inst[26:24]
                             , al_inst[20:17]
                           }
                         ;
  //==========================================================================
  // AL-state instruction decode
  //
  // 'al_inst_is_*' indicates the presence of a successfully decoded
  // instruction in AL, it DOES NOT imply the validity of the
  // instruction nor whether the instruction is to be passed to DA
  // during the current cycle.
  //
  al_inst_is_rtie   = 1'b0;
  al_inst_is_enter  = 1'b0;

  casez (al_inst)
    `npuarc_UOP_INST_RTIE:    al_inst_is_rtie      = al_pass;
    `npuarc_UOP_INST_ENTER_S: al_inst_is_enter     = 1'b1
                                        & (~da_uop_sirq_busy_case)
                                        ;
    default: ;
  endcase
// spyglass enable_block W193


  //==========================================================================
  // Current instruction in AL is an RTIE which will initiate a
  // slow-interrupt epilogue sequence.
  //
  al_uop_is_irtie        = 1'b0
  
                           | sirq_epil
                         ;

  //==========================================================================
  // AL stage RTIE initiates an Exception epilogue.
  //
  al_uop_is_ertie        = excpn_epil
                         ;

  //==========================================================================
  // Detect invalid ENTER-op instruction encodings an implicitly
  // convert such instructions into NOPs to be flagged as invalid by
  // the instruction decode logic.
  //
  al_enter_is_illegal    = (da_uop_enter_u7_nxt[3:0] == 4'b1111)
                         ;

  //==========================================================================
  // AL-stage is an ENTER_S/LEAVE_S instruction and the operand is
  // non-zero (when u7 == 7'b0, the instruction is a NOP; when u7 ==
  // 15, the instruction is invalid - therefore do nothing).
  //
  al_uop_is_enter        =  al_inst_is_enter
                         & (~al_enter_is_illegal)
                         &  al_pass
                         & (|da_uop_enter_u7_nxt)
                         ;

  //==========================================================================
  // Op-bit indicating the ENTER-operation taking place (0 - LEAVE_S, 1
  // - ENTER_S) present (in the 32-bit word) at bit position 21.
  //
  al_enter_op            = al_inst[21]
                         & (~da_uop_sirq_busy_case)
                         ;

end // block: decode_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @cmd_PROC                                                                //
//                                                                          //
// Process to implement the logic which initiates the appropriate           //
// micro-op operation as a function of the input to the module.             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg                           xirq_epil;
always @*
begin: cmd_PROC

  //==========================================================================
  // Current instruction in AL is an RTIE that invokes an interrupt
  // epilogue sequence.
  // if there is misprediction prior to rtie we need to kill the epilogue
  //
// leda W563 off
// LMD: Reduction of single bit expression is redundant
// LJ:  IRQ_ACT_ACT_RANGE can be single/multiple bits
  xirq_epil         = al_inst_is_rtie
                    & (|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE])
                    & (~ar_aux_status32_r[`npuarc_AE_FLAG])
                    & (~fch_restart_mpd)
                    ;
// leda W563 on

  //==========================================================================
  // A Slow-Interrupt prologue sequence is initiated in the current
  // cycle.
  //
  sirq_prol         =  wa_restart_cmd_r[`npuarc_RSRT_IS_IRQ]
                    &  wa_restart_r
                    ;


  //==========================================================================
  // The instruction in AL is an RTIE and initiates a Slow-Interrupt
  // epilogue sequence.
  //
  sirq_epil         = xirq_epil
                    ;

  //==========================================================================
  // An exception prologue is initiated in the current cycle.
  //
  excpn_prol        = wa_restart_cmd_r[`npuarc_RSRT_IS_EXCPN]
                    & wa_restart_r
                    ;

  //==========================================================================
  // An exception prologue is initiated in the current cycle.
  //
  reset_prol        = wa_restart_cmd_r[`npuarc_RSRT_IS_RESET]
                    & wa_restart_r
                    ;

  //==========================================================================
  // The instruction in AL is an RTIE and initiates an exception
  // epilogue sequence.
  // if there is misprediction prior to rtie we need to kill the epilogue
  //
  excpn_epil        = al_inst_is_rtie
                    & (~fch_restart_mpd)
                    & (~(   1'b0
                         | sirq_epil
                       ))
                    ;

end // block: cmd_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to derived 'UOP_BUSY' to indicate the period       //
// over which the uop_seq is active (in the non-idle state). The next state //
// of the register is derived by the state of the uop_seq and/or any        //
// commands that it receives. Flow control is implemented on the register   //
// enable.                                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: uop_busy_PROC

  //==========================================================================
  // 'uop_busy' is set in response to either a CA restart command or on
  // the decode of a multi-op initiating instruction.
  //
  da_uop_busy_set   = (excpn_prol | excpn_epil | reset_prol)
                    | (sirq_prol | sirq_epil)
                    | al_uop_is_enter
                    ;

  da_uop_epil_busy_set = excpn_epil
                       | sirq_epil
                    ;


  //==========================================================================
  // 'uop_prmpt' is set in response to the preemption of a current
  // multi-op sequence by another if the sequencer is already busy.
  //
  da_uop_busy_prmpt = excpn_prol
                    | sirq_prol
                    ;

  //==========================================================================
  // 'uop_busy' is rescinded the cycle after either the completion of a
  // terminal state, or on a pipeline flush.
  //
  da_uop_busy_clr   = da_kill
                    | ( fch_restart_mpd & da_uop_epil_busy_r) 
                    | (   da_uop_base_r[`npuarc_UOP_BASE_IS_TERM]
                        | da_uop_sirq_r[`npuarc_UOP_SIRQ_IS_TERM]
                        | da_uop_enter_r[`npuarc_UOP_SIRQ_IS_TERM]
                      )
                    ;

  //==========================================================================
  // Derive 'uop_busy' as a simple SR-FF. Retain busy state if an
  // incoming multi-op request (on a WA restart) preempts a initiated,
  // speculative instruction.
  //
  da_uop_busy_nxt   = ( da_uop_busy_set                       & (~da_uop_busy_r))
                    | ((da_uop_busy_prmpt | (~da_uop_busy_clr)) &  da_uop_busy_r)
                    ;

  da_uop_epil_busy_nxt = da_uop_epil_busy_set
                       | ( ( ~da_uop_busy_clr) &  da_uop_epil_busy_r)
                       ;

end // block: uop_busy_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @pred_PROC:                                                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: pred_PROC

  //==========================================================================
  // Retain the associated prediction for the multi-op sequence when
  // the sequence to be emitted is sure to emit a CTI instruction,
  // otherwise for an associated prediction emit an error branch
  // misprediction.
  //
  expect_pred       = 1'b0
                    | (   al_uop_is_enter                        // LEAVE_S pcl
                        & (~al_enter_op)
                        & da_uop_enter_u7_nxt[`npuarc_OPD_BLINK_BIT]
                      )
                    | al_inst_is_rtie                            // RTIE
                    ;

  //==========================================================================
  // Enable UOP_SEQ prediction logic when snooping a valid multi-op
  // initiating instruction in AL.
  //
  da_uop_pred_cg0   = ~da_uop_busy_r
                    &  expect_pred
                    & ( (al_uop_is_enter & (~al_enter_op))      // LEAVE_S
                        | al_inst_is_rtie                       // RTIE
                      )
                    ;

  //==========================================================================
  // UOP snoops incoming pred from AL and retains it to be emitted to DA
  // on a jump instruction.
  //
  al_uop_snoops_pred= da_uop_pred_cg0
                    ;

end // block: pred_PROC



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @sirq_sp_cntrl_reg_PROC                                                  //
//                                                                          //
// AUX_IRQ_CTRL stack-pointer data path state.                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: sirq_sp_cntrl_reg_PROC
  if (rst_a == 1'b1) begin
    sirq_sp_cntrl_r <= 2'd0;
  end
  else begin
    sirq_sp_cntrl_r   <= sirq_sp_cntrl_nxt;
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
// UOP epilogue busy state                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: uop_epil_busy_PROC
  if (rst_a == 1'b1) begin
    da_uop_epil_busy_r   <= 1'b0;
  end
  else begin
    da_uop_epil_busy_r   <= da_uop_epil_busy_nxt;
  end
end

// leda W175 on

endmodule // uop_seq_al
