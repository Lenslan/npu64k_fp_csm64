// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2020 Synopsys, Inc. All rights reserved.
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
//   ###   #      ######        #####  #     #   ###   ######  #######
//  #   #  #      #     #      #       ##   ##  #   #  #     #    #
// #     # #      #     #      #       # # # # #     # #     #    #
// ####### #      ######        #####  #  #  # ####### #####      #
// #     # #      #     #            # #     # #     # #    #     #
// #     # #      #     #            # #     # #     # #    #     #
// #     # ###### ######  ####  #####  #     # #     # #     #    #
//
// ============================================================================
//
// Description:
//
//  This module implements the configurable SmaRT unit of the ARCv2HS CPU for
//  stack implementation option.  
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_smart.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

////////////////////////////////////////////////////////////////////////////
// wrapper to alb_smart module
// register monitored inputs to avoid critical timing
// 

// spyglass disable_block OneModule-ML
// SMD: more than 1 module in file
// SJ:  causes no issues

// Flip-flop stack implementation
module npuarc_alb_smart (

  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,              // clock
  input                       rst_a,            // asynchronous reset

  ////////// Interface for SR instructions to write aux regs ///////////////
  //         (WA stage)
  input                       aux_smt_wen_r,    // (WA) Aux write enable
  input                       aux_smt_waddr_r,  // (WA) Aux write Address
  input       [`npuarc_DATA_RANGE]   wa_sr_data_r,     // (WA) Aux write data

  ////////// Interface for aux address / perm checks and aux read //////////
  //         (X3 stage)
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Standard aux interface
  input                       aux_smt_active,   // (X3) Aux SMT active
  input                       aux_write,        // (X3) Aux write operation
// spyglass disable_block W240
// SMD: Input declared but not read
// SJ:  Unused ports, left for interface consistency
  input                       aux_read,         // (X3) Aux read operation
// spyglass enable_block W240
  input                       aux_smt_ren_r,    // (X3) Aux unit select
  input                       aux_smt_raddr_r,  // (X3) Aux address (rd/wr)
  // leda NTL_CON13C on
  output      [`npuarc_DATA_RANGE]   smt_aux_rdata,    // (X3) LR read data
  output                      smt_aux_illegal,  // (X3) SR/LR op is illegal
  output                      smt_aux_k_rd,     // (X3) op needs Kernel R perm
  output                      smt_aux_k_wr,     // (X3) op needs Kernel W perm
  output                      smt_aux_unimpl,   // (X3) LR/SR reg is not present
  output                      smt_aux_serial_sr,// (X3) SR group flush
  output                      smt_aux_strict_sr,// (X3) SR single flush

  ////////// Pipeline interface /////////////////////////////////////////
  //
  input                       ca_pass,
  input                       ca_pass_eslot,
  input                       ca_br_evt,
  input                       ca_trap_op_r,

  input       [`npuarc_PC_RANGE]     ar_pc_r,  
  input       [`npuarc_PC_RANGE]     ar_pc_nxt,  
  input       [`npuarc_PC_RANGE]     ca_pc_jump,       // jump instr address
  input       [`npuarc_PC_RANGE]     aux_eret_addr,    // exception return addr
  input       [`npuarc_PC_RANGE]     wa_pc_r,            

  output                      smt_cap_rst_vec,
  input       [`npuarc_PC_RANGE]     ar_pc_save_r, 

  input       [`npuarc_PC_RANGE]     ar_aux_lp_end_r, 
  input                       ca_user_mode_nxt,        

  input                       ca_excpn_prol_evt,
  input                       ca_excpn_enter_evt,

  input                       ca_int_prologue_evt,
  input                       ca_int_enter_evt,
  input                       ca_int_epilogue_evt,

  output                      smt_unit_enable,// for architectural clock gating
  input                       ca_lp_jmp_r
);


// declare delayed/registered input signals to monitor

reg                           rr_ca_pass;
reg                           rr_ca_pass_eslot;
reg                           rr_ca_br_evt;
reg                           rr_ca_trap_op_r;
reg                           rr_ca_lp_jmp_r;
reg                           rr_ca_user_mode_nxt;        

reg                           rr_ca_excpn_prol_evt;
reg                           rr_ca_excpn_enter_evt;

reg                           rr_ca_int_prologue_evt;
reg                           rr_ca_int_enter_evt;
reg                           rr_ca_int_epilogue_evt;

reg           [`npuarc_PC_RANGE]     rr_ar_pc_r;  
reg           [`npuarc_PC_RANGE]     rr_ar_pc_nxt;  
reg           [`npuarc_PC_RANGE]     rr_ca_pc_jump;      
reg           [`npuarc_PC_RANGE]     rr_aux_eret_addr;   
reg           [`npuarc_PC_RANGE]     rr_wa_pc_r;         
reg           [`npuarc_PC_RANGE]     rr_ar_aux_lp_end_r; 

wire                          smt_en;

always @(posedge clk or
         posedge rst_a)
begin:  smt_register_inputs_PROC
  if (rst_a == 1'b1)
  begin
    rr_ca_pass                  <= 1'b0;
    rr_ca_pass_eslot            <= 1'b0;
    rr_ca_br_evt                <= 1'b0;
    rr_ca_trap_op_r             <= 1'b0;
    rr_ca_lp_jmp_r              <= 1'b0;
    rr_ca_user_mode_nxt         <= 1'b0;

    rr_ca_excpn_prol_evt        <= 1'b0;
    rr_ca_excpn_enter_evt       <= 1'b0;

    rr_ca_int_prologue_evt      <= 1'b0;
    rr_ca_int_enter_evt         <= 1'b0;
    rr_ca_int_epilogue_evt      <= 1'b0;

    rr_ar_pc_r                  <= `npuarc_PC_SIZE'h0;
    rr_ar_pc_nxt                <= `npuarc_PC_SIZE'h0;
    rr_ca_pc_jump               <= `npuarc_PC_SIZE'h0;
    rr_aux_eret_addr            <= `npuarc_PC_SIZE'h0;
    rr_wa_pc_r                  <= `npuarc_PC_SIZE'h0;
    rr_ar_aux_lp_end_r          <= `npuarc_PC_SIZE'h0;
  end
  else
  if (smt_en)
  begin
    rr_ca_pass                  <= ca_pass;
    rr_ca_pass_eslot            <= ca_pass_eslot;
    rr_ca_br_evt                <= ca_br_evt;
    rr_ca_trap_op_r             <= ca_trap_op_r;
    rr_ca_lp_jmp_r              <= ca_lp_jmp_r;
    rr_ca_user_mode_nxt         <= ca_user_mode_nxt;

    rr_ca_excpn_prol_evt        <= ca_excpn_prol_evt;
    rr_ca_excpn_enter_evt       <= ca_excpn_enter_evt;

    rr_ca_int_prologue_evt      <= ca_int_prologue_evt;
    rr_ca_int_enter_evt         <= ca_int_enter_evt;
    rr_ca_int_epilogue_evt      <= ca_int_epilogue_evt;

    rr_ar_pc_r                  <= ar_pc_r;
    rr_ar_pc_nxt                <= ar_pc_nxt;
    rr_ca_pc_jump               <= ca_pc_jump;
    rr_aux_eret_addr            <= aux_eret_addr;
    rr_wa_pc_r                  <= wa_pc_r;
    rr_ar_aux_lp_end_r          <= ar_aux_lp_end_r;
  end
end  // smt_register_inputs_PROC


// instantiate the unified module

npuarc_alb_smart_unified u_smart (
  .clk                 (clk                   ),
  .rst_a               (rst_a                 ),

  // WA stage
  .aux_smt_wen_r       (aux_smt_wen_r         ),
  .aux_smt_waddr_r     (aux_smt_waddr_r       ),
  .wa_sr_data_r        (wa_sr_data_r          ),

  // X3 stage
  .aux_smt_active      (aux_smt_active        ),
  .aux_write           (aux_write             ),
  .aux_read            (aux_read              ),
  .aux_smt_ren_r       (aux_smt_ren_r         ),
  .aux_smt_raddr_r     (aux_smt_raddr_r       ),

  .smt_aux_rdata       (smt_aux_rdata         ),
  .smt_aux_illegal     (smt_aux_illegal       ),
  .smt_aux_k_rd        (smt_aux_k_rd          ),
  .smt_aux_k_wr        (smt_aux_k_wr          ),
  .smt_aux_unimpl      (smt_aux_unimpl        ),
  .smt_aux_serial_sr   (smt_aux_serial_sr     ),
  .smt_aux_strict_sr   (smt_aux_strict_sr     ),

  .ca_pass             (rr_ca_pass            ),   // delayed/registered input
  .ca_pass_eslot       (rr_ca_pass_eslot      ),   // delayed/registered input
  .ca_pc_jump          (rr_ca_pc_jump         ),   // delayed/registered input
  .aux_eret_addr       (rr_aux_eret_addr      ),   // delayed/registered input
  .ca_br_evt           (rr_ca_br_evt          ),   // delayed/registered input
  .ca_trap_op_r        (rr_ca_trap_op_r       ),   // delayed/registered input
  .ca_lp_jmp_r         (rr_ca_lp_jmp_r        ),   // delayed/registered input
  .ar_pc_r             (rr_ar_pc_r            ),   // delayed/registered input
  .ar_pc_nxt           (rr_ar_pc_nxt          ),   // delayed/registered input
  .wa_pc_r             (rr_wa_pc_r            ),   // delayed/registered input

  .smt_cap_rst_vec     (smt_cap_rst_vec       ),   // output
  .ar_pc_save_r        (ar_pc_save_r          ),   // delayed/registered input

  .ar_aux_lp_end_r     (rr_ar_aux_lp_end_r    ),   // delayed/registered input
  .ca_user_mode_nxt    (rr_ca_user_mode_nxt   ),   // delayed/registered input
  
  .ca_excpn_prol_evt   (rr_ca_excpn_prol_evt  ),   // delayed/registered input
  .ca_excpn_enter_evt  (rr_ca_excpn_enter_evt ),   // delayed/registered input
  .ca_int_prologue_evt (rr_ca_int_prologue_evt),   // delayed/registered input
  .ca_int_enter_evt    (rr_ca_int_enter_evt   ),   // delayed/registered input
  .ca_int_epilogue_evt (rr_ca_int_epilogue_evt),   // delayed/registered input

  
  .smt_unit_enable     (smt_unit_enable       ),
  .smt_en              (smt_en                )
);


endmodule // alb_smart




////////////////////////////////////////////////////////////////////////////
// Next is the original alb_smart module
// 
// 

module npuarc_alb_smart_unified (

  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,              // clock
  input                       rst_a,            // asynchronous reset

  ////////// Interface for SR instructions to write aux regs ///////////////
  //         (WA stage)
  input                       aux_smt_wen_r,    // (WA) Aux write enable
  input                       aux_smt_waddr_r,  // (WA) Aux write Address
  input       [`npuarc_DATA_RANGE]   wa_sr_data_r,     // (WA) Aux write data

  ////////// Interface for aux address / perm checks and aux read //////////
  //         (X3 stage)
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Standard aux interface
  input                       aux_smt_active,   // (X3) Aux SMT active
  input                       aux_write,        // (X3) Aux write operation
// spyglass disable_block W240
// SMD: Input declared but not read
// SJ:  Unused ports, left for interface consistency
  input                       aux_read,         // (X3) Aux read operation
// spyglass enable_block W240
  input                       aux_smt_ren_r,    // (X3) Aux unit select
  input                       aux_smt_raddr_r,  // (X3) Aux address (rd/wr)
  // leda NTL_CON13C on
  output reg  [`npuarc_DATA_RANGE]   smt_aux_rdata,    // (X3) LR read data
  output reg                  smt_aux_illegal,  // (X3) SR/LR op is illegal
  output reg                  smt_aux_k_rd,     // (X3) op needs Kernel R perm
  output reg                  smt_aux_k_wr,     // (X3) op needs Kernel W perm
  output reg                  smt_aux_unimpl,   // (X3) LR/SR reg is not present
  output reg                  smt_aux_serial_sr,// (X3) SR group flush
  output reg                  smt_aux_strict_sr,// (X3) SR single flush

  ////////// Pipeline interface /////////////////////////////////////////
  //
  input                       ca_pass,
  input                       ca_pass_eslot,
  input                       ca_br_evt,
  input                       ca_trap_op_r,
  input                       ca_lp_jmp_r,

  input       [`npuarc_PC_RANGE]     ar_pc_r,  
  input       [`npuarc_PC_RANGE]     ar_pc_nxt,  
  input       [`npuarc_PC_RANGE]     ca_pc_jump,       // jump instr address
  input       [`npuarc_PC_RANGE]     aux_eret_addr,    // exception return addr
  input       [`npuarc_PC_RANGE]     wa_pc_r,            

  output reg                  smt_cap_rst_vec,
  input       [`npuarc_PC_RANGE]     ar_pc_save_r,


  input       [`npuarc_PC_RANGE]     ar_aux_lp_end_r, 
  input                       ca_user_mode_nxt,        

  input                       ca_excpn_prol_evt,
  input                       ca_excpn_enter_evt,

  input                       ca_int_prologue_evt,
  input                       ca_int_enter_evt,
  input                       ca_int_epilogue_evt,

  output                      smt_unit_enable,// for architectural clock gating
  output                      smt_en
);

// Local declarations

reg                 aux_smt_ctrl_wen;
reg [`npuarc_DATA_RANGE]   aux_smt_ctrl_r;
reg  [31:1]         smt_ctrl_m_r;
reg                 smt_ctrl_l_r;
             
reg  [`npuarc_PC_RANGE]    smt_src_addr0;
reg  [`npuarc_PC_RANGE]    smt_dst_addr0;
reg  [`npuarc_DATA_RANGE]  smt_flags0;

reg  [`npuarc_PC_RANGE]    smt_src_addr1;
reg  [`npuarc_PC_RANGE]    smt_dst_addr1;
reg  [`npuarc_DATA_RANGE]  smt_flags1;

reg  [`npuarc_PC_RANGE]    smt_src_addr2;
reg  [`npuarc_PC_RANGE]    smt_dst_addr2;
reg  [`npuarc_DATA_RANGE]  smt_flags2;

reg  [`npuarc_PC_RANGE]    smt_src_addr3;
reg  [`npuarc_PC_RANGE]    smt_dst_addr3;
reg  [`npuarc_DATA_RANGE]  smt_flags3;

reg  [`npuarc_PC_RANGE]    smt_src_addr4;
reg  [`npuarc_PC_RANGE]    smt_dst_addr4;
reg  [`npuarc_DATA_RANGE]  smt_flags4;

reg  [`npuarc_PC_RANGE]    smt_src_addr5;
reg  [`npuarc_PC_RANGE]    smt_dst_addr5;
reg  [`npuarc_DATA_RANGE]  smt_flags5;

reg  [`npuarc_PC_RANGE]    smt_src_addr6;
reg  [`npuarc_PC_RANGE]    smt_dst_addr6;
reg  [`npuarc_DATA_RANGE]  smt_flags6;

reg  [`npuarc_PC_RANGE]    smt_src_addr7;
reg  [`npuarc_PC_RANGE]    smt_dst_addr7;
reg  [`npuarc_DATA_RANGE]  smt_flags7;

reg  [`npuarc_PC_RANGE]    smt_src_addr8;
reg  [`npuarc_PC_RANGE]    smt_dst_addr8;
reg  [`npuarc_DATA_RANGE]  smt_flags8;

reg  [`npuarc_PC_RANGE]    smt_src_addr9;
reg  [`npuarc_PC_RANGE]    smt_dst_addr9;
reg  [`npuarc_DATA_RANGE]  smt_flags9;

reg  [`npuarc_PC_RANGE]    smt_src_addr10;
reg  [`npuarc_PC_RANGE]    smt_dst_addr10;
reg  [`npuarc_DATA_RANGE]  smt_flags10;

reg  [`npuarc_PC_RANGE]    smt_src_addr11;
reg  [`npuarc_PC_RANGE]    smt_dst_addr11;
reg  [`npuarc_DATA_RANGE]  smt_flags11;

reg  [`npuarc_PC_RANGE]    smt_src_addr12;
reg  [`npuarc_PC_RANGE]    smt_dst_addr12;
reg  [`npuarc_DATA_RANGE]  smt_flags12;

reg  [`npuarc_PC_RANGE]    smt_src_addr13;
reg  [`npuarc_PC_RANGE]    smt_dst_addr13;
reg  [`npuarc_DATA_RANGE]  smt_flags13;

reg  [`npuarc_PC_RANGE]    smt_src_addr14;
reg  [`npuarc_PC_RANGE]    smt_dst_addr14;
reg  [`npuarc_DATA_RANGE]  smt_flags14;

reg  [`npuarc_PC_RANGE]    smt_src_addr15;
reg  [`npuarc_PC_RANGE]    smt_dst_addr15;
reg  [`npuarc_DATA_RANGE]  smt_flags15;

reg  [`npuarc_PC_RANGE]    smt_src_addr16;
reg  [`npuarc_PC_RANGE]    smt_dst_addr16;
reg  [`npuarc_DATA_RANGE]  smt_flags16;

reg  [`npuarc_PC_RANGE]    smt_src_addr17;
reg  [`npuarc_PC_RANGE]    smt_dst_addr17;
reg  [`npuarc_DATA_RANGE]  smt_flags17;

reg  [`npuarc_PC_RANGE]    smt_src_addr18;
reg  [`npuarc_PC_RANGE]    smt_dst_addr18;
reg  [`npuarc_DATA_RANGE]  smt_flags18;

reg  [`npuarc_PC_RANGE]    smt_src_addr19;
reg  [`npuarc_PC_RANGE]    smt_dst_addr19;
reg  [`npuarc_DATA_RANGE]  smt_flags19;

reg  [`npuarc_PC_RANGE]    smt_src_addr20;
reg  [`npuarc_PC_RANGE]    smt_dst_addr20;
reg  [`npuarc_DATA_RANGE]  smt_flags20;

reg  [`npuarc_PC_RANGE]    smt_src_addr21;
reg  [`npuarc_PC_RANGE]    smt_dst_addr21;
reg  [`npuarc_DATA_RANGE]  smt_flags21;

reg  [`npuarc_PC_RANGE]    smt_src_addr22;
reg  [`npuarc_PC_RANGE]    smt_dst_addr22;
reg  [`npuarc_DATA_RANGE]  smt_flags22;

reg  [`npuarc_PC_RANGE]    smt_src_addr23;
reg  [`npuarc_PC_RANGE]    smt_dst_addr23;
reg  [`npuarc_DATA_RANGE]  smt_flags23;

reg  [`npuarc_PC_RANGE]    smt_src_addr24;
reg  [`npuarc_PC_RANGE]    smt_dst_addr24;
reg  [`npuarc_DATA_RANGE]  smt_flags24;

reg  [`npuarc_PC_RANGE]    smt_src_addr25;
reg  [`npuarc_PC_RANGE]    smt_dst_addr25;
reg  [`npuarc_DATA_RANGE]  smt_flags25;

reg  [`npuarc_PC_RANGE]    smt_src_addr26;
reg  [`npuarc_PC_RANGE]    smt_dst_addr26;
reg  [`npuarc_DATA_RANGE]  smt_flags26;

reg  [`npuarc_PC_RANGE]    smt_src_addr27;
reg  [`npuarc_PC_RANGE]    smt_dst_addr27;
reg  [`npuarc_DATA_RANGE]  smt_flags27;

reg  [`npuarc_PC_RANGE]    smt_src_addr28;
reg  [`npuarc_PC_RANGE]    smt_dst_addr28;
reg  [`npuarc_DATA_RANGE]  smt_flags28;

reg  [`npuarc_PC_RANGE]    smt_src_addr29;
reg  [`npuarc_PC_RANGE]    smt_dst_addr29;
reg  [`npuarc_DATA_RANGE]  smt_flags29;

reg  [`npuarc_PC_RANGE]    smt_src_addr30;
reg  [`npuarc_PC_RANGE]    smt_dst_addr30;
reg  [`npuarc_DATA_RANGE]  smt_flags30;

reg  [`npuarc_PC_RANGE]    smt_src_addr31;
reg  [`npuarc_PC_RANGE]    smt_dst_addr31;
reg  [`npuarc_DATA_RANGE]  smt_flags31;

reg  [`npuarc_PC_RANGE]    smt_src_addr32;
reg  [`npuarc_PC_RANGE]    smt_dst_addr32;
reg  [`npuarc_DATA_RANGE]  smt_flags32;

reg  [`npuarc_PC_RANGE]    smt_src_addr33;
reg  [`npuarc_PC_RANGE]    smt_dst_addr33;
reg  [`npuarc_DATA_RANGE]  smt_flags33;

reg  [`npuarc_PC_RANGE]    smt_src_addr34;
reg  [`npuarc_PC_RANGE]    smt_dst_addr34;
reg  [`npuarc_DATA_RANGE]  smt_flags34;

reg  [`npuarc_PC_RANGE]    smt_src_addr35;
reg  [`npuarc_PC_RANGE]    smt_dst_addr35;
reg  [`npuarc_DATA_RANGE]  smt_flags35;

reg  [`npuarc_PC_RANGE]    smt_src_addr36;
reg  [`npuarc_PC_RANGE]    smt_dst_addr36;
reg  [`npuarc_DATA_RANGE]  smt_flags36;

reg  [`npuarc_PC_RANGE]    smt_src_addr37;
reg  [`npuarc_PC_RANGE]    smt_dst_addr37;
reg  [`npuarc_DATA_RANGE]  smt_flags37;

reg  [`npuarc_PC_RANGE]    smt_src_addr38;
reg  [`npuarc_PC_RANGE]    smt_dst_addr38;
reg  [`npuarc_DATA_RANGE]  smt_flags38;

reg  [`npuarc_PC_RANGE]    smt_src_addr39;
reg  [`npuarc_PC_RANGE]    smt_dst_addr39;
reg  [`npuarc_DATA_RANGE]  smt_flags39;

reg  [`npuarc_PC_RANGE]    smt_src_addr40;
reg  [`npuarc_PC_RANGE]    smt_dst_addr40;
reg  [`npuarc_DATA_RANGE]  smt_flags40;

reg  [`npuarc_PC_RANGE]    smt_src_addr41;
reg  [`npuarc_PC_RANGE]    smt_dst_addr41;
reg  [`npuarc_DATA_RANGE]  smt_flags41;

reg  [`npuarc_PC_RANGE]    smt_src_addr42;
reg  [`npuarc_PC_RANGE]    smt_dst_addr42;
reg  [`npuarc_DATA_RANGE]  smt_flags42;

reg  [`npuarc_PC_RANGE]    smt_src_addr43;
reg  [`npuarc_PC_RANGE]    smt_dst_addr43;
reg  [`npuarc_DATA_RANGE]  smt_flags43;

reg  [`npuarc_PC_RANGE]    smt_src_addr44;
reg  [`npuarc_PC_RANGE]    smt_dst_addr44;
reg  [`npuarc_DATA_RANGE]  smt_flags44;

reg  [`npuarc_PC_RANGE]    smt_src_addr45;
reg  [`npuarc_PC_RANGE]    smt_dst_addr45;
reg  [`npuarc_DATA_RANGE]  smt_flags45;

reg  [`npuarc_PC_RANGE]    smt_src_addr46;
reg  [`npuarc_PC_RANGE]    smt_dst_addr46;
reg  [`npuarc_DATA_RANGE]  smt_flags46;

reg  [`npuarc_PC_RANGE]    smt_src_addr47;
reg  [`npuarc_PC_RANGE]    smt_dst_addr47;
reg  [`npuarc_DATA_RANGE]  smt_flags47;

reg  [`npuarc_PC_RANGE]    smt_src_addr48;
reg  [`npuarc_PC_RANGE]    smt_dst_addr48;
reg  [`npuarc_DATA_RANGE]  smt_flags48;

reg  [`npuarc_PC_RANGE]    smt_src_addr49;
reg  [`npuarc_PC_RANGE]    smt_dst_addr49;
reg  [`npuarc_DATA_RANGE]  smt_flags49;

reg  [`npuarc_PC_RANGE]    smt_src_addr50;
reg  [`npuarc_PC_RANGE]    smt_dst_addr50;
reg  [`npuarc_DATA_RANGE]  smt_flags50;

reg  [`npuarc_PC_RANGE]    smt_src_addr51;
reg  [`npuarc_PC_RANGE]    smt_dst_addr51;
reg  [`npuarc_DATA_RANGE]  smt_flags51;

reg  [`npuarc_PC_RANGE]    smt_src_addr52;
reg  [`npuarc_PC_RANGE]    smt_dst_addr52;
reg  [`npuarc_DATA_RANGE]  smt_flags52;

reg  [`npuarc_PC_RANGE]    smt_src_addr53;
reg  [`npuarc_PC_RANGE]    smt_dst_addr53;
reg  [`npuarc_DATA_RANGE]  smt_flags53;

reg  [`npuarc_PC_RANGE]    smt_src_addr54;
reg  [`npuarc_PC_RANGE]    smt_dst_addr54;
reg  [`npuarc_DATA_RANGE]  smt_flags54;

reg  [`npuarc_PC_RANGE]    smt_src_addr55;
reg  [`npuarc_PC_RANGE]    smt_dst_addr55;
reg  [`npuarc_DATA_RANGE]  smt_flags55;

reg  [`npuarc_PC_RANGE]    smt_src_addr56;
reg  [`npuarc_PC_RANGE]    smt_dst_addr56;
reg  [`npuarc_DATA_RANGE]  smt_flags56;

reg  [`npuarc_PC_RANGE]    smt_src_addr57;
reg  [`npuarc_PC_RANGE]    smt_dst_addr57;
reg  [`npuarc_DATA_RANGE]  smt_flags57;

reg  [`npuarc_PC_RANGE]    smt_src_addr58;
reg  [`npuarc_PC_RANGE]    smt_dst_addr58;
reg  [`npuarc_DATA_RANGE]  smt_flags58;

reg  [`npuarc_PC_RANGE]    smt_src_addr59;
reg  [`npuarc_PC_RANGE]    smt_dst_addr59;
reg  [`npuarc_DATA_RANGE]  smt_flags59;

reg  [`npuarc_PC_RANGE]    smt_src_addr60;
reg  [`npuarc_PC_RANGE]    smt_dst_addr60;
reg  [`npuarc_DATA_RANGE]  smt_flags60;

reg  [`npuarc_PC_RANGE]    smt_src_addr61;
reg  [`npuarc_PC_RANGE]    smt_dst_addr61;
reg  [`npuarc_DATA_RANGE]  smt_flags61;

reg  [`npuarc_PC_RANGE]    smt_src_addr62;
reg  [`npuarc_PC_RANGE]    smt_dst_addr62;
reg  [`npuarc_DATA_RANGE]  smt_flags62;

reg  [`npuarc_PC_RANGE]    smt_src_addr63;
reg  [`npuarc_PC_RANGE]    smt_dst_addr63;
reg  [`npuarc_DATA_RANGE]  smt_flags63;

reg  [`npuarc_PC_RANGE]    smt_src_addr64;
reg  [`npuarc_PC_RANGE]    smt_dst_addr64;
reg  [`npuarc_DATA_RANGE]  smt_flags64;

reg  [`npuarc_PC_RANGE]    smt_src_addr65;
reg  [`npuarc_PC_RANGE]    smt_dst_addr65;
reg  [`npuarc_DATA_RANGE]  smt_flags65;

reg  [`npuarc_PC_RANGE]    smt_src_addr66;
reg  [`npuarc_PC_RANGE]    smt_dst_addr66;
reg  [`npuarc_DATA_RANGE]  smt_flags66;

reg  [`npuarc_PC_RANGE]    smt_src_addr67;
reg  [`npuarc_PC_RANGE]    smt_dst_addr67;
reg  [`npuarc_DATA_RANGE]  smt_flags67;

reg  [`npuarc_PC_RANGE]    smt_src_addr68;
reg  [`npuarc_PC_RANGE]    smt_dst_addr68;
reg  [`npuarc_DATA_RANGE]  smt_flags68;

reg  [`npuarc_PC_RANGE]    smt_src_addr69;
reg  [`npuarc_PC_RANGE]    smt_dst_addr69;
reg  [`npuarc_DATA_RANGE]  smt_flags69;

reg  [`npuarc_PC_RANGE]    smt_src_addr70;
reg  [`npuarc_PC_RANGE]    smt_dst_addr70;
reg  [`npuarc_DATA_RANGE]  smt_flags70;

reg  [`npuarc_PC_RANGE]    smt_src_addr71;
reg  [`npuarc_PC_RANGE]    smt_dst_addr71;
reg  [`npuarc_DATA_RANGE]  smt_flags71;

reg  [`npuarc_PC_RANGE]    smt_src_addr72;
reg  [`npuarc_PC_RANGE]    smt_dst_addr72;
reg  [`npuarc_DATA_RANGE]  smt_flags72;

reg  [`npuarc_PC_RANGE]    smt_src_addr73;
reg  [`npuarc_PC_RANGE]    smt_dst_addr73;
reg  [`npuarc_DATA_RANGE]  smt_flags73;

reg  [`npuarc_PC_RANGE]    smt_src_addr74;
reg  [`npuarc_PC_RANGE]    smt_dst_addr74;
reg  [`npuarc_DATA_RANGE]  smt_flags74;

reg  [`npuarc_PC_RANGE]    smt_src_addr75;
reg  [`npuarc_PC_RANGE]    smt_dst_addr75;
reg  [`npuarc_DATA_RANGE]  smt_flags75;

reg  [`npuarc_PC_RANGE]    smt_src_addr76;
reg  [`npuarc_PC_RANGE]    smt_dst_addr76;
reg  [`npuarc_DATA_RANGE]  smt_flags76;

reg  [`npuarc_PC_RANGE]    smt_src_addr77;
reg  [`npuarc_PC_RANGE]    smt_dst_addr77;
reg  [`npuarc_DATA_RANGE]  smt_flags77;

reg  [`npuarc_PC_RANGE]    smt_src_addr78;
reg  [`npuarc_PC_RANGE]    smt_dst_addr78;
reg  [`npuarc_DATA_RANGE]  smt_flags78;

reg  [`npuarc_PC_RANGE]    smt_src_addr79;
reg  [`npuarc_PC_RANGE]    smt_dst_addr79;
reg  [`npuarc_DATA_RANGE]  smt_flags79;

reg  [`npuarc_PC_RANGE]    smt_src_addr80;
reg  [`npuarc_PC_RANGE]    smt_dst_addr80;
reg  [`npuarc_DATA_RANGE]  smt_flags80;

reg  [`npuarc_PC_RANGE]    smt_src_addr81;
reg  [`npuarc_PC_RANGE]    smt_dst_addr81;
reg  [`npuarc_DATA_RANGE]  smt_flags81;

reg  [`npuarc_PC_RANGE]    smt_src_addr82;
reg  [`npuarc_PC_RANGE]    smt_dst_addr82;
reg  [`npuarc_DATA_RANGE]  smt_flags82;

reg  [`npuarc_PC_RANGE]    smt_src_addr83;
reg  [`npuarc_PC_RANGE]    smt_dst_addr83;
reg  [`npuarc_DATA_RANGE]  smt_flags83;

reg  [`npuarc_PC_RANGE]    smt_src_addr84;
reg  [`npuarc_PC_RANGE]    smt_dst_addr84;
reg  [`npuarc_DATA_RANGE]  smt_flags84;

reg  [`npuarc_PC_RANGE]    smt_src_addr85;
reg  [`npuarc_PC_RANGE]    smt_dst_addr85;
reg  [`npuarc_DATA_RANGE]  smt_flags85;

reg  [`npuarc_PC_RANGE]    smt_src_addr86;
reg  [`npuarc_PC_RANGE]    smt_dst_addr86;
reg  [`npuarc_DATA_RANGE]  smt_flags86;

reg  [`npuarc_PC_RANGE]    smt_src_addr87;
reg  [`npuarc_PC_RANGE]    smt_dst_addr87;
reg  [`npuarc_DATA_RANGE]  smt_flags87;

reg  [`npuarc_PC_RANGE]    smt_src_addr88;
reg  [`npuarc_PC_RANGE]    smt_dst_addr88;
reg  [`npuarc_DATA_RANGE]  smt_flags88;

reg  [`npuarc_PC_RANGE]    smt_src_addr89;
reg  [`npuarc_PC_RANGE]    smt_dst_addr89;
reg  [`npuarc_DATA_RANGE]  smt_flags89;

reg  [`npuarc_PC_RANGE]    smt_src_addr90;
reg  [`npuarc_PC_RANGE]    smt_dst_addr90;
reg  [`npuarc_DATA_RANGE]  smt_flags90;

reg  [`npuarc_PC_RANGE]    smt_src_addr91;
reg  [`npuarc_PC_RANGE]    smt_dst_addr91;
reg  [`npuarc_DATA_RANGE]  smt_flags91;

reg  [`npuarc_PC_RANGE]    smt_src_addr92;
reg  [`npuarc_PC_RANGE]    smt_dst_addr92;
reg  [`npuarc_DATA_RANGE]  smt_flags92;

reg  [`npuarc_PC_RANGE]    smt_src_addr93;
reg  [`npuarc_PC_RANGE]    smt_dst_addr93;
reg  [`npuarc_DATA_RANGE]  smt_flags93;

reg  [`npuarc_PC_RANGE]    smt_src_addr94;
reg  [`npuarc_PC_RANGE]    smt_dst_addr94;
reg  [`npuarc_DATA_RANGE]  smt_flags94;

reg  [`npuarc_PC_RANGE]    smt_src_addr95;
reg  [`npuarc_PC_RANGE]    smt_dst_addr95;
reg  [`npuarc_DATA_RANGE]  smt_flags95;

reg  [`npuarc_PC_RANGE]    smt_src_addr96;
reg  [`npuarc_PC_RANGE]    smt_dst_addr96;
reg  [`npuarc_DATA_RANGE]  smt_flags96;

reg  [`npuarc_PC_RANGE]    smt_src_addr97;
reg  [`npuarc_PC_RANGE]    smt_dst_addr97;
reg  [`npuarc_DATA_RANGE]  smt_flags97;

reg  [`npuarc_PC_RANGE]    smt_src_addr98;
reg  [`npuarc_PC_RANGE]    smt_dst_addr98;
reg  [`npuarc_DATA_RANGE]  smt_flags98;

reg  [`npuarc_PC_RANGE]    smt_src_addr99;
reg  [`npuarc_PC_RANGE]    smt_dst_addr99;
reg  [`npuarc_DATA_RANGE]  smt_flags99;

reg  [`npuarc_PC_RANGE]    smt_src_addr100;
reg  [`npuarc_PC_RANGE]    smt_dst_addr100;
reg  [`npuarc_DATA_RANGE]  smt_flags100;

reg  [`npuarc_PC_RANGE]    smt_src_addr101;
reg  [`npuarc_PC_RANGE]    smt_dst_addr101;
reg  [`npuarc_DATA_RANGE]  smt_flags101;

reg  [`npuarc_PC_RANGE]    smt_src_addr102;
reg  [`npuarc_PC_RANGE]    smt_dst_addr102;
reg  [`npuarc_DATA_RANGE]  smt_flags102;

reg  [`npuarc_PC_RANGE]    smt_src_addr103;
reg  [`npuarc_PC_RANGE]    smt_dst_addr103;
reg  [`npuarc_DATA_RANGE]  smt_flags103;

reg  [`npuarc_PC_RANGE]    smt_src_addr104;
reg  [`npuarc_PC_RANGE]    smt_dst_addr104;
reg  [`npuarc_DATA_RANGE]  smt_flags104;

reg  [`npuarc_PC_RANGE]    smt_src_addr105;
reg  [`npuarc_PC_RANGE]    smt_dst_addr105;
reg  [`npuarc_DATA_RANGE]  smt_flags105;

reg  [`npuarc_PC_RANGE]    smt_src_addr106;
reg  [`npuarc_PC_RANGE]    smt_dst_addr106;
reg  [`npuarc_DATA_RANGE]  smt_flags106;

reg  [`npuarc_PC_RANGE]    smt_src_addr107;
reg  [`npuarc_PC_RANGE]    smt_dst_addr107;
reg  [`npuarc_DATA_RANGE]  smt_flags107;

reg  [`npuarc_PC_RANGE]    smt_src_addr108;
reg  [`npuarc_PC_RANGE]    smt_dst_addr108;
reg  [`npuarc_DATA_RANGE]  smt_flags108;

reg  [`npuarc_PC_RANGE]    smt_src_addr109;
reg  [`npuarc_PC_RANGE]    smt_dst_addr109;
reg  [`npuarc_DATA_RANGE]  smt_flags109;

reg  [`npuarc_PC_RANGE]    smt_src_addr110;
reg  [`npuarc_PC_RANGE]    smt_dst_addr110;
reg  [`npuarc_DATA_RANGE]  smt_flags110;

reg  [`npuarc_PC_RANGE]    smt_src_addr111;
reg  [`npuarc_PC_RANGE]    smt_dst_addr111;
reg  [`npuarc_DATA_RANGE]  smt_flags111;

reg  [`npuarc_PC_RANGE]    smt_src_addr112;
reg  [`npuarc_PC_RANGE]    smt_dst_addr112;
reg  [`npuarc_DATA_RANGE]  smt_flags112;

reg  [`npuarc_PC_RANGE]    smt_src_addr113;
reg  [`npuarc_PC_RANGE]    smt_dst_addr113;
reg  [`npuarc_DATA_RANGE]  smt_flags113;

reg  [`npuarc_PC_RANGE]    smt_src_addr114;
reg  [`npuarc_PC_RANGE]    smt_dst_addr114;
reg  [`npuarc_DATA_RANGE]  smt_flags114;

reg  [`npuarc_PC_RANGE]    smt_src_addr115;
reg  [`npuarc_PC_RANGE]    smt_dst_addr115;
reg  [`npuarc_DATA_RANGE]  smt_flags115;

reg  [`npuarc_PC_RANGE]    smt_src_addr116;
reg  [`npuarc_PC_RANGE]    smt_dst_addr116;
reg  [`npuarc_DATA_RANGE]  smt_flags116;

reg  [`npuarc_PC_RANGE]    smt_src_addr117;
reg  [`npuarc_PC_RANGE]    smt_dst_addr117;
reg  [`npuarc_DATA_RANGE]  smt_flags117;

reg  [`npuarc_PC_RANGE]    smt_src_addr118;
reg  [`npuarc_PC_RANGE]    smt_dst_addr118;
reg  [`npuarc_DATA_RANGE]  smt_flags118;

reg  [`npuarc_PC_RANGE]    smt_src_addr119;
reg  [`npuarc_PC_RANGE]    smt_dst_addr119;
reg  [`npuarc_DATA_RANGE]  smt_flags119;

reg  [`npuarc_PC_RANGE]    smt_src_addr120;
reg  [`npuarc_PC_RANGE]    smt_dst_addr120;
reg  [`npuarc_DATA_RANGE]  smt_flags120;

reg  [`npuarc_PC_RANGE]    smt_src_addr121;
reg  [`npuarc_PC_RANGE]    smt_dst_addr121;
reg  [`npuarc_DATA_RANGE]  smt_flags121;

reg  [`npuarc_PC_RANGE]    smt_src_addr122;
reg  [`npuarc_PC_RANGE]    smt_dst_addr122;
reg  [`npuarc_DATA_RANGE]  smt_flags122;

reg  [`npuarc_PC_RANGE]    smt_src_addr123;
reg  [`npuarc_PC_RANGE]    smt_dst_addr123;
reg  [`npuarc_DATA_RANGE]  smt_flags123;

reg  [`npuarc_PC_RANGE]    smt_src_addr124;
reg  [`npuarc_PC_RANGE]    smt_dst_addr124;
reg  [`npuarc_DATA_RANGE]  smt_flags124;

reg  [`npuarc_PC_RANGE]    smt_src_addr125;
reg  [`npuarc_PC_RANGE]    smt_dst_addr125;
reg  [`npuarc_DATA_RANGE]  smt_flags125;

reg  [`npuarc_PC_RANGE]    smt_src_addr126;
reg  [`npuarc_PC_RANGE]    smt_dst_addr126;
reg  [`npuarc_DATA_RANGE]  smt_flags126;

reg  [`npuarc_PC_RANGE]    smt_src_addr127;
reg  [`npuarc_PC_RANGE]    smt_dst_addr127;
reg  [`npuarc_DATA_RANGE]  smt_flags127;

reg  [`npuarc_PC_RANGE]    int_or_exc_src_addr_r;
reg  [`npuarc_PC_RANGE]    trap_src_addr_r;
reg  [`npuarc_PC_RANGE]    smt_stack_src_addr;
reg  [`npuarc_PC_RANGE]    smt_stack_dst_addr;
reg  [`npuarc_DATA_RANGE]  smt_stack_flags;

reg  [`npuarc_DATA_RANGE]  smt_stack_data;


reg                 rst_e;   // reset upon smart enable if was disabled


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Auxiliary registers, next state, select and write enable signals       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : smart_reg_rd_PROC

  smt_aux_rdata         = `npuarc_DATA_SIZE'h0;
  smt_aux_k_rd          = 1'b0;
  smt_aux_k_wr          = 1'b0;
  smt_aux_unimpl        = 1'b1;
  smt_aux_illegal       = 1'b0;
  smt_aux_serial_sr     = 1'b0;
  smt_aux_strict_sr     = 1'b0;

  if (aux_smt_ren_r) 
  begin
    case ({11'b0111_0000_000,aux_smt_raddr_r}) // single bit

    `npuarc_SRT_CTRL_AUX: // K_RW
    begin
      smt_aux_rdata     = {aux_smt_ctrl_r[31:10], // location pointer
                           aux_smt_ctrl_r[9:8],   // location index
                           7'h0,
                           aux_smt_ctrl_r[0]};    // enable
      smt_aux_k_rd      = 1'b1;
      smt_aux_k_wr      = 1'b1;
      smt_aux_unimpl    = 1'b0;
      smt_aux_serial_sr = aux_write;
    end

    `npuarc_SRT_DATA_AUX: // K_READ
    begin
      smt_aux_rdata     = smt_stack_data;
      smt_aux_k_rd      = 1'b1;
      smt_aux_unimpl    = 1'b0;
      smt_aux_illegal   = aux_write;
    end

    default:
    begin
      smt_aux_unimpl    = 1'b1;
      smt_aux_serial_sr = 1'b0;
      smt_aux_strict_sr = 1'b0;
    end
    endcase
  end

end // block: smart_reg_rd_PROC

always @*
begin : smart_reg_wr_PROC

  aux_smt_ctrl_wen      = 1'b0;

  if (aux_smt_wen_r) 
  begin
    
    case ({11'b0111_0000_000, aux_smt_waddr_r}) // single bit
    `npuarc_SRT_CTRL_AUX: // K_RW
    begin
      aux_smt_ctrl_wen  = 1'b1;
    end

    default:
    begin
      aux_smt_ctrl_wen  = 1'b0;
    end
    endcase
  end

end // block: smart_reg_wr_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining SmaRT auxiliary registers                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_smt_ctrl_PROC

  aux_smt_ctrl_r = {smt_ctrl_m_r, smt_ctrl_l_r};

end // block : aux_smt_ctrl_PROC

// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected 
// SJ:  Constraints need to ensure the sync timing
// spyglass disable_block STARC-2.3.4.3
// SMD: (Recommended) Flip-flop has neither asynchronous set nor asynchronous reset
// SJ:  The intention of this register is to retain its value after reset
always @(posedge clk)
begin : smt_ctrl_m_reg_PROC
  if (aux_smt_ctrl_wen)
  begin
    smt_ctrl_m_r[31:1]    <= wa_sr_data_r[31:1];
  end
end // block :  smt_ctrl_m_reg_PROC
// spyglass enable_block STARC-2.3.4.3
// spyglass enable_block Ar_resetcross01

always @(posedge clk or
         posedge rst_a)
begin : wa_sr_data_PROC
  if (rst_a == 1'b1)
  begin
    smt_ctrl_l_r      <= 1'b0;  // disable tracing
    rst_e             <= 1'b0;  // internal reset for buffer and pointers
  end
  else
  if (aux_smt_ctrl_wen)
  begin
    smt_ctrl_l_r      <= wa_sr_data_r[0];
    rst_e             <= wa_sr_data_r[0] & ~aux_smt_ctrl_r[0];
                                // transition from disabled to enabled
  end
  else
  begin
    rst_e             <= 1'b0;
  end
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// SmaRT Stack                                                            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


// ctl signals
//
wire ca_jump_taken;
wire ca_int_or_exc_taken;
wire ca_int_or_exc_prologue;
wire ca_loop_taken;
wire smt_clock_en;

reg  trap_excpn_req_r;
reg  trap_excpn_prol_r;
reg  wa_lpj_taken;
reg  wa_lp_taken;
reg  wa_smt_cg0;
wire smt_set_rp;
reg  wa_int_or_exc_prologue_r;
wire ca_smt_cg0;
reg smt_cap_1c_rst_r;
reg smt_cap_2c_rst_r;


assign ca_jump_taken       = (ca_pass | ca_pass_eslot)
                           & ca_br_evt & (~ca_trap_op_r)
                           ;

assign ca_int_or_exc_taken    =  ca_excpn_enter_evt
                              |  ca_int_enter_evt
                              ;
assign ca_int_or_exc_prologue = (  ca_excpn_prol_evt
                                 & (~trap_excpn_prol_r)) // already captured source address for trap
                              | ca_int_prologue_evt
                              | ( ca_trap_op_r           // capture trap source address
                                 & ca_pass) 
                              ;

assign ca_loop_taken       =   ca_pass
                             & ca_lp_jmp_r;


assign smt_clock_en        =  (aux_smt_ctrl_r[0]
                             & (  ca_jump_taken
                                | ca_int_or_exc_taken
                                | ca_loop_taken
                               ))
                           | (smt_cap_rst_vec & ca_jump_taken)
                           ;


// Data signals
//

wire [`npuarc_PC_RANGE] ca_src_addr;
wire [`npuarc_PC_RANGE] ca_dst_addr;

assign ca_src_addr = (ca_trap_op_r && ca_pass)        ? ca_pc_jump      :    // 
                     trap_excpn_prol_r                ? trap_src_addr_r :
                     ca_excpn_enter_evt               ? aux_eret_addr   :
                     ca_int_enter_evt                 ? ar_pc_r         :
                     ca_pass_eslot                    ? smt_dst_addr0   :    // src of return from EI is the dest of EI
                     (ca_loop_taken & !ca_jump_taken) ? ar_aux_lp_end_r :
                                                        ar_pc_r
                   ;
assign ca_dst_addr = ar_pc_nxt;

// small state machine to capture trap src address upon ca_trap_op_r
// keeps trap status until prolog ends, resets status if encounters ca_pass before prolog start
//
// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected 
// SJ:  Constraints need to ensure the sync timing
// spyglass disable_block STARC-2.3.4.3
// SMD: (Recommended) Flip-flop has neither asynchronous set nor asynchronous reset
// SJ:  The intention of this register is to retain its value after reset
always @(posedge clk)
begin:  smt_trap_src_PROC
  if (ca_smt_cg0 && ca_trap_op_r && aux_smt_ctrl_r[0])
  begin
    trap_src_addr_r   <= ar_pc_r;
  end
end
// spyglass enable_block STARC-2.3.4.3
// spyglass enable_block Ar_resetcross01
//
always @(posedge clk or
         posedge rst_a)
begin:  smt_trap_excpn_prol_PROC
  if (rst_a == 1'b1)
  begin
    trap_excpn_req_r  <= 1'b0;
    trap_excpn_prol_r <= 1'b0;
  end
  else
  if (ca_smt_cg0 && ca_trap_op_r && aux_smt_ctrl_r[0])
  begin
    trap_excpn_req_r  <= 1'b1;
    trap_excpn_prol_r <= 1'b0;
  end
  else
  if (trap_excpn_req_r && ca_excpn_prol_evt)
  begin
    trap_excpn_req_r  <= 1'b0;
    trap_excpn_prol_r <= 1'b1;
  end
  else
  if (ca_excpn_enter_evt && trap_excpn_prol_r)
  begin
    trap_excpn_prol_r <= 1'b0;
  end
end

// The repeat flag will be set when the most recent stack entry (entry0)
// already has the same src and dst address of the new coming loop info.
//

assign smt_set_rp =    smt_flags0[31]                   // valid
                    & (ca_loop_taken | ca_jump_taken)
                    & (ca_src_addr == smt_src_addr0)
                    & (ca_dst_addr == smt_dst_addr0)
                    ;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining SmaRT Stack Entries                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

wire wa_int_excpn_cg0;
assign wa_int_excpn_cg0 = wa_int_or_exc_prologue_r;
assign ca_smt_cg0       = ca_pass | ca_pass_eslot;

// spyglass disable_block STARC-2.3.4.3
// SMD: (Recommended) Flip-flop has neither asynchronous set nor asynchronous reset
// SJ:  The intention of this register is to retain its value after reset
// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected 
// SJ:  Functionally Flop is gated off during reset
// spyglass enable_block Ar_resetcross01
// spyglass enable_block STARC-2.3.4.3

always @(posedge clk or
         posedge rst_a)
begin : wa_smt_en_PROC
  if (rst_a == 1'b1)
  begin
    wa_smt_cg0            <= 1'b0;
    wa_lpj_taken          <= 1'b0;
    wa_lp_taken           <= 1'b0;
    smt_cap_rst_vec       <= 1'b1;
    smt_cap_1c_rst_r      <= 1'b1;
    smt_cap_2c_rst_r      <= 1'b0;
  end
  else
  begin
    if (ca_smt_cg0)
    begin
      wa_smt_cg0            <= smt_clock_en;
      wa_lpj_taken          <= (ca_loop_taken | ca_jump_taken);
      wa_lp_taken           <= (ca_loop_taken & (~ca_jump_taken));
      if (ca_jump_taken == 1'b1)
        smt_cap_rst_vec     <= 1'b0;
    end
    else
    begin
      wa_smt_cg0            <= 1'b0;
    end
    smt_cap_1c_rst_r        <= 1'b0;
    smt_cap_2c_rst_r        <= smt_cap_1c_rst_r;
  end
end // block : wa_smt_en_PROC

always @(posedge clk or
         posedge rst_a)
begin : wa_prolg_PROC
  if (rst_a == 1'b1)
    wa_int_or_exc_prologue_r <= 1'b0;
  else if (wa_int_excpn_cg0)
    wa_int_or_exc_prologue_r <= ca_int_or_exc_prologue;
end // block : wa_prolg_PROC

// capture source address for interrupt or exception
//
always @(posedge clk or
         posedge rst_a)
begin:  smt_int_src_adr_PROC
  if (rst_a == 1'b1)
    int_or_exc_src_addr_r <= `npuarc_PC_BITS'h0;
  else if (wa_int_or_exc_prologue_r)
    int_or_exc_src_addr_r <= wa_pc_r;
end

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: AsyncResetOrSet Recommended
// SJ:  init value not required for data
always @(posedge clk)
begin:  smt_entry_regs_PROC
  if (rst_e == 1'b1)     // resets synchronously one clock after smart is enabled
  begin
        smt_src_addr0 <= `npuarc_PC_BITS'h0;
        smt_dst_addr0 <= `npuarc_PC_BITS'h0;
        smt_flags0    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr1 <= `npuarc_PC_BITS'h0;
        smt_dst_addr1 <= `npuarc_PC_BITS'h0;
        smt_flags1    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr2 <= `npuarc_PC_BITS'h0;
        smt_dst_addr2 <= `npuarc_PC_BITS'h0;
        smt_flags2    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr3 <= `npuarc_PC_BITS'h0;
        smt_dst_addr3 <= `npuarc_PC_BITS'h0;
        smt_flags3    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr4 <= `npuarc_PC_BITS'h0;
        smt_dst_addr4 <= `npuarc_PC_BITS'h0;
        smt_flags4    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr5 <= `npuarc_PC_BITS'h0;
        smt_dst_addr5 <= `npuarc_PC_BITS'h0;
        smt_flags5    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr6 <= `npuarc_PC_BITS'h0;
        smt_dst_addr6 <= `npuarc_PC_BITS'h0;
        smt_flags6    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr7 <= `npuarc_PC_BITS'h0;
        smt_dst_addr7 <= `npuarc_PC_BITS'h0;
        smt_flags7    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr8 <= `npuarc_PC_BITS'h0;
        smt_dst_addr8 <= `npuarc_PC_BITS'h0;
        smt_flags8    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr9 <= `npuarc_PC_BITS'h0;
        smt_dst_addr9 <= `npuarc_PC_BITS'h0;
        smt_flags9    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr10 <= `npuarc_PC_BITS'h0;
        smt_dst_addr10 <= `npuarc_PC_BITS'h0;
        smt_flags10    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr11 <= `npuarc_PC_BITS'h0;
        smt_dst_addr11 <= `npuarc_PC_BITS'h0;
        smt_flags11    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr12 <= `npuarc_PC_BITS'h0;
        smt_dst_addr12 <= `npuarc_PC_BITS'h0;
        smt_flags12    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr13 <= `npuarc_PC_BITS'h0;
        smt_dst_addr13 <= `npuarc_PC_BITS'h0;
        smt_flags13    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr14 <= `npuarc_PC_BITS'h0;
        smt_dst_addr14 <= `npuarc_PC_BITS'h0;
        smt_flags14    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr15 <= `npuarc_PC_BITS'h0;
        smt_dst_addr15 <= `npuarc_PC_BITS'h0;
        smt_flags15    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr16 <= `npuarc_PC_BITS'h0;
        smt_dst_addr16 <= `npuarc_PC_BITS'h0;
        smt_flags16    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr17 <= `npuarc_PC_BITS'h0;
        smt_dst_addr17 <= `npuarc_PC_BITS'h0;
        smt_flags17    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr18 <= `npuarc_PC_BITS'h0;
        smt_dst_addr18 <= `npuarc_PC_BITS'h0;
        smt_flags18    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr19 <= `npuarc_PC_BITS'h0;
        smt_dst_addr19 <= `npuarc_PC_BITS'h0;
        smt_flags19    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr20 <= `npuarc_PC_BITS'h0;
        smt_dst_addr20 <= `npuarc_PC_BITS'h0;
        smt_flags20    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr21 <= `npuarc_PC_BITS'h0;
        smt_dst_addr21 <= `npuarc_PC_BITS'h0;
        smt_flags21    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr22 <= `npuarc_PC_BITS'h0;
        smt_dst_addr22 <= `npuarc_PC_BITS'h0;
        smt_flags22    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr23 <= `npuarc_PC_BITS'h0;
        smt_dst_addr23 <= `npuarc_PC_BITS'h0;
        smt_flags23    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr24 <= `npuarc_PC_BITS'h0;
        smt_dst_addr24 <= `npuarc_PC_BITS'h0;
        smt_flags24    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr25 <= `npuarc_PC_BITS'h0;
        smt_dst_addr25 <= `npuarc_PC_BITS'h0;
        smt_flags25    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr26 <= `npuarc_PC_BITS'h0;
        smt_dst_addr26 <= `npuarc_PC_BITS'h0;
        smt_flags26    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr27 <= `npuarc_PC_BITS'h0;
        smt_dst_addr27 <= `npuarc_PC_BITS'h0;
        smt_flags27    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr28 <= `npuarc_PC_BITS'h0;
        smt_dst_addr28 <= `npuarc_PC_BITS'h0;
        smt_flags28    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr29 <= `npuarc_PC_BITS'h0;
        smt_dst_addr29 <= `npuarc_PC_BITS'h0;
        smt_flags29    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr30 <= `npuarc_PC_BITS'h0;
        smt_dst_addr30 <= `npuarc_PC_BITS'h0;
        smt_flags30    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr31 <= `npuarc_PC_BITS'h0;
        smt_dst_addr31 <= `npuarc_PC_BITS'h0;
        smt_flags31    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr32 <= `npuarc_PC_BITS'h0;
        smt_dst_addr32 <= `npuarc_PC_BITS'h0;
        smt_flags32    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr33 <= `npuarc_PC_BITS'h0;
        smt_dst_addr33 <= `npuarc_PC_BITS'h0;
        smt_flags33    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr34 <= `npuarc_PC_BITS'h0;
        smt_dst_addr34 <= `npuarc_PC_BITS'h0;
        smt_flags34    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr35 <= `npuarc_PC_BITS'h0;
        smt_dst_addr35 <= `npuarc_PC_BITS'h0;
        smt_flags35    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr36 <= `npuarc_PC_BITS'h0;
        smt_dst_addr36 <= `npuarc_PC_BITS'h0;
        smt_flags36    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr37 <= `npuarc_PC_BITS'h0;
        smt_dst_addr37 <= `npuarc_PC_BITS'h0;
        smt_flags37    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr38 <= `npuarc_PC_BITS'h0;
        smt_dst_addr38 <= `npuarc_PC_BITS'h0;
        smt_flags38    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr39 <= `npuarc_PC_BITS'h0;
        smt_dst_addr39 <= `npuarc_PC_BITS'h0;
        smt_flags39    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr40 <= `npuarc_PC_BITS'h0;
        smt_dst_addr40 <= `npuarc_PC_BITS'h0;
        smt_flags40    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr41 <= `npuarc_PC_BITS'h0;
        smt_dst_addr41 <= `npuarc_PC_BITS'h0;
        smt_flags41    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr42 <= `npuarc_PC_BITS'h0;
        smt_dst_addr42 <= `npuarc_PC_BITS'h0;
        smt_flags42    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr43 <= `npuarc_PC_BITS'h0;
        smt_dst_addr43 <= `npuarc_PC_BITS'h0;
        smt_flags43    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr44 <= `npuarc_PC_BITS'h0;
        smt_dst_addr44 <= `npuarc_PC_BITS'h0;
        smt_flags44    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr45 <= `npuarc_PC_BITS'h0;
        smt_dst_addr45 <= `npuarc_PC_BITS'h0;
        smt_flags45    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr46 <= `npuarc_PC_BITS'h0;
        smt_dst_addr46 <= `npuarc_PC_BITS'h0;
        smt_flags46    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr47 <= `npuarc_PC_BITS'h0;
        smt_dst_addr47 <= `npuarc_PC_BITS'h0;
        smt_flags47    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr48 <= `npuarc_PC_BITS'h0;
        smt_dst_addr48 <= `npuarc_PC_BITS'h0;
        smt_flags48    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr49 <= `npuarc_PC_BITS'h0;
        smt_dst_addr49 <= `npuarc_PC_BITS'h0;
        smt_flags49    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr50 <= `npuarc_PC_BITS'h0;
        smt_dst_addr50 <= `npuarc_PC_BITS'h0;
        smt_flags50    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr51 <= `npuarc_PC_BITS'h0;
        smt_dst_addr51 <= `npuarc_PC_BITS'h0;
        smt_flags51    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr52 <= `npuarc_PC_BITS'h0;
        smt_dst_addr52 <= `npuarc_PC_BITS'h0;
        smt_flags52    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr53 <= `npuarc_PC_BITS'h0;
        smt_dst_addr53 <= `npuarc_PC_BITS'h0;
        smt_flags53    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr54 <= `npuarc_PC_BITS'h0;
        smt_dst_addr54 <= `npuarc_PC_BITS'h0;
        smt_flags54    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr55 <= `npuarc_PC_BITS'h0;
        smt_dst_addr55 <= `npuarc_PC_BITS'h0;
        smt_flags55    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr56 <= `npuarc_PC_BITS'h0;
        smt_dst_addr56 <= `npuarc_PC_BITS'h0;
        smt_flags56    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr57 <= `npuarc_PC_BITS'h0;
        smt_dst_addr57 <= `npuarc_PC_BITS'h0;
        smt_flags57    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr58 <= `npuarc_PC_BITS'h0;
        smt_dst_addr58 <= `npuarc_PC_BITS'h0;
        smt_flags58    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr59 <= `npuarc_PC_BITS'h0;
        smt_dst_addr59 <= `npuarc_PC_BITS'h0;
        smt_flags59    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr60 <= `npuarc_PC_BITS'h0;
        smt_dst_addr60 <= `npuarc_PC_BITS'h0;
        smt_flags60    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr61 <= `npuarc_PC_BITS'h0;
        smt_dst_addr61 <= `npuarc_PC_BITS'h0;
        smt_flags61    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr62 <= `npuarc_PC_BITS'h0;
        smt_dst_addr62 <= `npuarc_PC_BITS'h0;
        smt_flags62    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr63 <= `npuarc_PC_BITS'h0;
        smt_dst_addr63 <= `npuarc_PC_BITS'h0;
        smt_flags63    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr64 <= `npuarc_PC_BITS'h0;
        smt_dst_addr64 <= `npuarc_PC_BITS'h0;
        smt_flags64    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr65 <= `npuarc_PC_BITS'h0;
        smt_dst_addr65 <= `npuarc_PC_BITS'h0;
        smt_flags65    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr66 <= `npuarc_PC_BITS'h0;
        smt_dst_addr66 <= `npuarc_PC_BITS'h0;
        smt_flags66    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr67 <= `npuarc_PC_BITS'h0;
        smt_dst_addr67 <= `npuarc_PC_BITS'h0;
        smt_flags67    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr68 <= `npuarc_PC_BITS'h0;
        smt_dst_addr68 <= `npuarc_PC_BITS'h0;
        smt_flags68    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr69 <= `npuarc_PC_BITS'h0;
        smt_dst_addr69 <= `npuarc_PC_BITS'h0;
        smt_flags69    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr70 <= `npuarc_PC_BITS'h0;
        smt_dst_addr70 <= `npuarc_PC_BITS'h0;
        smt_flags70    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr71 <= `npuarc_PC_BITS'h0;
        smt_dst_addr71 <= `npuarc_PC_BITS'h0;
        smt_flags71    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr72 <= `npuarc_PC_BITS'h0;
        smt_dst_addr72 <= `npuarc_PC_BITS'h0;
        smt_flags72    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr73 <= `npuarc_PC_BITS'h0;
        smt_dst_addr73 <= `npuarc_PC_BITS'h0;
        smt_flags73    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr74 <= `npuarc_PC_BITS'h0;
        smt_dst_addr74 <= `npuarc_PC_BITS'h0;
        smt_flags74    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr75 <= `npuarc_PC_BITS'h0;
        smt_dst_addr75 <= `npuarc_PC_BITS'h0;
        smt_flags75    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr76 <= `npuarc_PC_BITS'h0;
        smt_dst_addr76 <= `npuarc_PC_BITS'h0;
        smt_flags76    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr77 <= `npuarc_PC_BITS'h0;
        smt_dst_addr77 <= `npuarc_PC_BITS'h0;
        smt_flags77    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr78 <= `npuarc_PC_BITS'h0;
        smt_dst_addr78 <= `npuarc_PC_BITS'h0;
        smt_flags78    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr79 <= `npuarc_PC_BITS'h0;
        smt_dst_addr79 <= `npuarc_PC_BITS'h0;
        smt_flags79    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr80 <= `npuarc_PC_BITS'h0;
        smt_dst_addr80 <= `npuarc_PC_BITS'h0;
        smt_flags80    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr81 <= `npuarc_PC_BITS'h0;
        smt_dst_addr81 <= `npuarc_PC_BITS'h0;
        smt_flags81    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr82 <= `npuarc_PC_BITS'h0;
        smt_dst_addr82 <= `npuarc_PC_BITS'h0;
        smt_flags82    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr83 <= `npuarc_PC_BITS'h0;
        smt_dst_addr83 <= `npuarc_PC_BITS'h0;
        smt_flags83    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr84 <= `npuarc_PC_BITS'h0;
        smt_dst_addr84 <= `npuarc_PC_BITS'h0;
        smt_flags84    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr85 <= `npuarc_PC_BITS'h0;
        smt_dst_addr85 <= `npuarc_PC_BITS'h0;
        smt_flags85    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr86 <= `npuarc_PC_BITS'h0;
        smt_dst_addr86 <= `npuarc_PC_BITS'h0;
        smt_flags86    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr87 <= `npuarc_PC_BITS'h0;
        smt_dst_addr87 <= `npuarc_PC_BITS'h0;
        smt_flags87    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr88 <= `npuarc_PC_BITS'h0;
        smt_dst_addr88 <= `npuarc_PC_BITS'h0;
        smt_flags88    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr89 <= `npuarc_PC_BITS'h0;
        smt_dst_addr89 <= `npuarc_PC_BITS'h0;
        smt_flags89    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr90 <= `npuarc_PC_BITS'h0;
        smt_dst_addr90 <= `npuarc_PC_BITS'h0;
        smt_flags90    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr91 <= `npuarc_PC_BITS'h0;
        smt_dst_addr91 <= `npuarc_PC_BITS'h0;
        smt_flags91    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr92 <= `npuarc_PC_BITS'h0;
        smt_dst_addr92 <= `npuarc_PC_BITS'h0;
        smt_flags92    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr93 <= `npuarc_PC_BITS'h0;
        smt_dst_addr93 <= `npuarc_PC_BITS'h0;
        smt_flags93    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr94 <= `npuarc_PC_BITS'h0;
        smt_dst_addr94 <= `npuarc_PC_BITS'h0;
        smt_flags94    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr95 <= `npuarc_PC_BITS'h0;
        smt_dst_addr95 <= `npuarc_PC_BITS'h0;
        smt_flags95    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr96 <= `npuarc_PC_BITS'h0;
        smt_dst_addr96 <= `npuarc_PC_BITS'h0;
        smt_flags96    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr97 <= `npuarc_PC_BITS'h0;
        smt_dst_addr97 <= `npuarc_PC_BITS'h0;
        smt_flags97    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr98 <= `npuarc_PC_BITS'h0;
        smt_dst_addr98 <= `npuarc_PC_BITS'h0;
        smt_flags98    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr99 <= `npuarc_PC_BITS'h0;
        smt_dst_addr99 <= `npuarc_PC_BITS'h0;
        smt_flags99    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr100 <= `npuarc_PC_BITS'h0;
        smt_dst_addr100 <= `npuarc_PC_BITS'h0;
        smt_flags100    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr101 <= `npuarc_PC_BITS'h0;
        smt_dst_addr101 <= `npuarc_PC_BITS'h0;
        smt_flags101    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr102 <= `npuarc_PC_BITS'h0;
        smt_dst_addr102 <= `npuarc_PC_BITS'h0;
        smt_flags102    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr103 <= `npuarc_PC_BITS'h0;
        smt_dst_addr103 <= `npuarc_PC_BITS'h0;
        smt_flags103    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr104 <= `npuarc_PC_BITS'h0;
        smt_dst_addr104 <= `npuarc_PC_BITS'h0;
        smt_flags104    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr105 <= `npuarc_PC_BITS'h0;
        smt_dst_addr105 <= `npuarc_PC_BITS'h0;
        smt_flags105    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr106 <= `npuarc_PC_BITS'h0;
        smt_dst_addr106 <= `npuarc_PC_BITS'h0;
        smt_flags106    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr107 <= `npuarc_PC_BITS'h0;
        smt_dst_addr107 <= `npuarc_PC_BITS'h0;
        smt_flags107    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr108 <= `npuarc_PC_BITS'h0;
        smt_dst_addr108 <= `npuarc_PC_BITS'h0;
        smt_flags108    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr109 <= `npuarc_PC_BITS'h0;
        smt_dst_addr109 <= `npuarc_PC_BITS'h0;
        smt_flags109    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr110 <= `npuarc_PC_BITS'h0;
        smt_dst_addr110 <= `npuarc_PC_BITS'h0;
        smt_flags110    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr111 <= `npuarc_PC_BITS'h0;
        smt_dst_addr111 <= `npuarc_PC_BITS'h0;
        smt_flags111    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr112 <= `npuarc_PC_BITS'h0;
        smt_dst_addr112 <= `npuarc_PC_BITS'h0;
        smt_flags112    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr113 <= `npuarc_PC_BITS'h0;
        smt_dst_addr113 <= `npuarc_PC_BITS'h0;
        smt_flags113    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr114 <= `npuarc_PC_BITS'h0;
        smt_dst_addr114 <= `npuarc_PC_BITS'h0;
        smt_flags114    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr115 <= `npuarc_PC_BITS'h0;
        smt_dst_addr115 <= `npuarc_PC_BITS'h0;
        smt_flags115    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr116 <= `npuarc_PC_BITS'h0;
        smt_dst_addr116 <= `npuarc_PC_BITS'h0;
        smt_flags116    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr117 <= `npuarc_PC_BITS'h0;
        smt_dst_addr117 <= `npuarc_PC_BITS'h0;
        smt_flags117    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr118 <= `npuarc_PC_BITS'h0;
        smt_dst_addr118 <= `npuarc_PC_BITS'h0;
        smt_flags118    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr119 <= `npuarc_PC_BITS'h0;
        smt_dst_addr119 <= `npuarc_PC_BITS'h0;
        smt_flags119    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr120 <= `npuarc_PC_BITS'h0;
        smt_dst_addr120 <= `npuarc_PC_BITS'h0;
        smt_flags120    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr121 <= `npuarc_PC_BITS'h0;
        smt_dst_addr121 <= `npuarc_PC_BITS'h0;
        smt_flags121    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr122 <= `npuarc_PC_BITS'h0;
        smt_dst_addr122 <= `npuarc_PC_BITS'h0;
        smt_flags122    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr123 <= `npuarc_PC_BITS'h0;
        smt_dst_addr123 <= `npuarc_PC_BITS'h0;
        smt_flags123    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr124 <= `npuarc_PC_BITS'h0;
        smt_dst_addr124 <= `npuarc_PC_BITS'h0;
        smt_flags124    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr125 <= `npuarc_PC_BITS'h0;
        smt_dst_addr125 <= `npuarc_PC_BITS'h0;
        smt_flags125    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr126 <= `npuarc_PC_BITS'h0;
        smt_dst_addr126 <= `npuarc_PC_BITS'h0;
        smt_flags126    <= `npuarc_DATA_SIZE'h0;
        smt_src_addr127 <= `npuarc_PC_BITS'h0;
        smt_dst_addr127 <= `npuarc_PC_BITS'h0;
        smt_flags127    <= `npuarc_DATA_SIZE'h0;
  end
  else
  begin
//
    if ((ca_smt_cg0 && smt_clock_en) || (smt_cap_2c_rst_r == 1'b1))
    begin

      // Put new entry at the bottom and shift stack up
      //

      if (!smt_set_rp)
      begin
      // Advance the stack
      //
        smt_src_addr1 <= smt_src_addr0;
        smt_dst_addr1 <= smt_dst_addr0;
        smt_flags1    <= smt_flags0;

        smt_src_addr2 <= smt_src_addr1;
        smt_dst_addr2 <= smt_dst_addr1;
        smt_flags2    <= smt_flags1;

        smt_src_addr3 <= smt_src_addr2;
        smt_dst_addr3 <= smt_dst_addr2;
        smt_flags3    <= smt_flags2;

        smt_src_addr4 <= smt_src_addr3;
        smt_dst_addr4 <= smt_dst_addr3;
        smt_flags4    <= smt_flags3;

        smt_src_addr5 <= smt_src_addr4;
        smt_dst_addr5 <= smt_dst_addr4;
        smt_flags5    <= smt_flags4;

        smt_src_addr6 <= smt_src_addr5;
        smt_dst_addr6 <= smt_dst_addr5;
        smt_flags6    <= smt_flags5;

        smt_src_addr7 <= smt_src_addr6;
        smt_dst_addr7 <= smt_dst_addr6;
        smt_flags7    <= smt_flags6;

        smt_src_addr8 <= smt_src_addr7;
        smt_dst_addr8 <= smt_dst_addr7;
        smt_flags8    <= smt_flags7;

        smt_src_addr9 <= smt_src_addr8;
        smt_dst_addr9 <= smt_dst_addr8;
        smt_flags9    <= smt_flags8;

        smt_src_addr10 <= smt_src_addr9;
        smt_dst_addr10 <= smt_dst_addr9;
        smt_flags10    <= smt_flags9;

        smt_src_addr11 <= smt_src_addr10;
        smt_dst_addr11 <= smt_dst_addr10;
        smt_flags11    <= smt_flags10;

        smt_src_addr12 <= smt_src_addr11;
        smt_dst_addr12 <= smt_dst_addr11;
        smt_flags12    <= smt_flags11;

        smt_src_addr13 <= smt_src_addr12;
        smt_dst_addr13 <= smt_dst_addr12;
        smt_flags13    <= smt_flags12;

        smt_src_addr14 <= smt_src_addr13;
        smt_dst_addr14 <= smt_dst_addr13;
        smt_flags14    <= smt_flags13;

        smt_src_addr15 <= smt_src_addr14;
        smt_dst_addr15 <= smt_dst_addr14;
        smt_flags15    <= smt_flags14;

        smt_src_addr16 <= smt_src_addr15;
        smt_dst_addr16 <= smt_dst_addr15;
        smt_flags16    <= smt_flags15;

        smt_src_addr17 <= smt_src_addr16;
        smt_dst_addr17 <= smt_dst_addr16;
        smt_flags17    <= smt_flags16;

        smt_src_addr18 <= smt_src_addr17;
        smt_dst_addr18 <= smt_dst_addr17;
        smt_flags18    <= smt_flags17;

        smt_src_addr19 <= smt_src_addr18;
        smt_dst_addr19 <= smt_dst_addr18;
        smt_flags19    <= smt_flags18;

        smt_src_addr20 <= smt_src_addr19;
        smt_dst_addr20 <= smt_dst_addr19;
        smt_flags20    <= smt_flags19;

        smt_src_addr21 <= smt_src_addr20;
        smt_dst_addr21 <= smt_dst_addr20;
        smt_flags21    <= smt_flags20;

        smt_src_addr22 <= smt_src_addr21;
        smt_dst_addr22 <= smt_dst_addr21;
        smt_flags22    <= smt_flags21;

        smt_src_addr23 <= smt_src_addr22;
        smt_dst_addr23 <= smt_dst_addr22;
        smt_flags23    <= smt_flags22;

        smt_src_addr24 <= smt_src_addr23;
        smt_dst_addr24 <= smt_dst_addr23;
        smt_flags24    <= smt_flags23;

        smt_src_addr25 <= smt_src_addr24;
        smt_dst_addr25 <= smt_dst_addr24;
        smt_flags25    <= smt_flags24;

        smt_src_addr26 <= smt_src_addr25;
        smt_dst_addr26 <= smt_dst_addr25;
        smt_flags26    <= smt_flags25;

        smt_src_addr27 <= smt_src_addr26;
        smt_dst_addr27 <= smt_dst_addr26;
        smt_flags27    <= smt_flags26;

        smt_src_addr28 <= smt_src_addr27;
        smt_dst_addr28 <= smt_dst_addr27;
        smt_flags28    <= smt_flags27;

        smt_src_addr29 <= smt_src_addr28;
        smt_dst_addr29 <= smt_dst_addr28;
        smt_flags29    <= smt_flags28;

        smt_src_addr30 <= smt_src_addr29;
        smt_dst_addr30 <= smt_dst_addr29;
        smt_flags30    <= smt_flags29;

        smt_src_addr31 <= smt_src_addr30;
        smt_dst_addr31 <= smt_dst_addr30;
        smt_flags31    <= smt_flags30;

        smt_src_addr32 <= smt_src_addr31;
        smt_dst_addr32 <= smt_dst_addr31;
        smt_flags32    <= smt_flags31;

        smt_src_addr33 <= smt_src_addr32;
        smt_dst_addr33 <= smt_dst_addr32;
        smt_flags33    <= smt_flags32;

        smt_src_addr34 <= smt_src_addr33;
        smt_dst_addr34 <= smt_dst_addr33;
        smt_flags34    <= smt_flags33;

        smt_src_addr35 <= smt_src_addr34;
        smt_dst_addr35 <= smt_dst_addr34;
        smt_flags35    <= smt_flags34;

        smt_src_addr36 <= smt_src_addr35;
        smt_dst_addr36 <= smt_dst_addr35;
        smt_flags36    <= smt_flags35;

        smt_src_addr37 <= smt_src_addr36;
        smt_dst_addr37 <= smt_dst_addr36;
        smt_flags37    <= smt_flags36;

        smt_src_addr38 <= smt_src_addr37;
        smt_dst_addr38 <= smt_dst_addr37;
        smt_flags38    <= smt_flags37;

        smt_src_addr39 <= smt_src_addr38;
        smt_dst_addr39 <= smt_dst_addr38;
        smt_flags39    <= smt_flags38;

        smt_src_addr40 <= smt_src_addr39;
        smt_dst_addr40 <= smt_dst_addr39;
        smt_flags40    <= smt_flags39;

        smt_src_addr41 <= smt_src_addr40;
        smt_dst_addr41 <= smt_dst_addr40;
        smt_flags41    <= smt_flags40;

        smt_src_addr42 <= smt_src_addr41;
        smt_dst_addr42 <= smt_dst_addr41;
        smt_flags42    <= smt_flags41;

        smt_src_addr43 <= smt_src_addr42;
        smt_dst_addr43 <= smt_dst_addr42;
        smt_flags43    <= smt_flags42;

        smt_src_addr44 <= smt_src_addr43;
        smt_dst_addr44 <= smt_dst_addr43;
        smt_flags44    <= smt_flags43;

        smt_src_addr45 <= smt_src_addr44;
        smt_dst_addr45 <= smt_dst_addr44;
        smt_flags45    <= smt_flags44;

        smt_src_addr46 <= smt_src_addr45;
        smt_dst_addr46 <= smt_dst_addr45;
        smt_flags46    <= smt_flags45;

        smt_src_addr47 <= smt_src_addr46;
        smt_dst_addr47 <= smt_dst_addr46;
        smt_flags47    <= smt_flags46;

        smt_src_addr48 <= smt_src_addr47;
        smt_dst_addr48 <= smt_dst_addr47;
        smt_flags48    <= smt_flags47;

        smt_src_addr49 <= smt_src_addr48;
        smt_dst_addr49 <= smt_dst_addr48;
        smt_flags49    <= smt_flags48;

        smt_src_addr50 <= smt_src_addr49;
        smt_dst_addr50 <= smt_dst_addr49;
        smt_flags50    <= smt_flags49;

        smt_src_addr51 <= smt_src_addr50;
        smt_dst_addr51 <= smt_dst_addr50;
        smt_flags51    <= smt_flags50;

        smt_src_addr52 <= smt_src_addr51;
        smt_dst_addr52 <= smt_dst_addr51;
        smt_flags52    <= smt_flags51;

        smt_src_addr53 <= smt_src_addr52;
        smt_dst_addr53 <= smt_dst_addr52;
        smt_flags53    <= smt_flags52;

        smt_src_addr54 <= smt_src_addr53;
        smt_dst_addr54 <= smt_dst_addr53;
        smt_flags54    <= smt_flags53;

        smt_src_addr55 <= smt_src_addr54;
        smt_dst_addr55 <= smt_dst_addr54;
        smt_flags55    <= smt_flags54;

        smt_src_addr56 <= smt_src_addr55;
        smt_dst_addr56 <= smt_dst_addr55;
        smt_flags56    <= smt_flags55;

        smt_src_addr57 <= smt_src_addr56;
        smt_dst_addr57 <= smt_dst_addr56;
        smt_flags57    <= smt_flags56;

        smt_src_addr58 <= smt_src_addr57;
        smt_dst_addr58 <= smt_dst_addr57;
        smt_flags58    <= smt_flags57;

        smt_src_addr59 <= smt_src_addr58;
        smt_dst_addr59 <= smt_dst_addr58;
        smt_flags59    <= smt_flags58;

        smt_src_addr60 <= smt_src_addr59;
        smt_dst_addr60 <= smt_dst_addr59;
        smt_flags60    <= smt_flags59;

        smt_src_addr61 <= smt_src_addr60;
        smt_dst_addr61 <= smt_dst_addr60;
        smt_flags61    <= smt_flags60;

        smt_src_addr62 <= smt_src_addr61;
        smt_dst_addr62 <= smt_dst_addr61;
        smt_flags62    <= smt_flags61;

        smt_src_addr63 <= smt_src_addr62;
        smt_dst_addr63 <= smt_dst_addr62;
        smt_flags63    <= smt_flags62;

        smt_src_addr64 <= smt_src_addr63;
        smt_dst_addr64 <= smt_dst_addr63;
        smt_flags64    <= smt_flags63;

        smt_src_addr65 <= smt_src_addr64;
        smt_dst_addr65 <= smt_dst_addr64;
        smt_flags65    <= smt_flags64;

        smt_src_addr66 <= smt_src_addr65;
        smt_dst_addr66 <= smt_dst_addr65;
        smt_flags66    <= smt_flags65;

        smt_src_addr67 <= smt_src_addr66;
        smt_dst_addr67 <= smt_dst_addr66;
        smt_flags67    <= smt_flags66;

        smt_src_addr68 <= smt_src_addr67;
        smt_dst_addr68 <= smt_dst_addr67;
        smt_flags68    <= smt_flags67;

        smt_src_addr69 <= smt_src_addr68;
        smt_dst_addr69 <= smt_dst_addr68;
        smt_flags69    <= smt_flags68;

        smt_src_addr70 <= smt_src_addr69;
        smt_dst_addr70 <= smt_dst_addr69;
        smt_flags70    <= smt_flags69;

        smt_src_addr71 <= smt_src_addr70;
        smt_dst_addr71 <= smt_dst_addr70;
        smt_flags71    <= smt_flags70;

        smt_src_addr72 <= smt_src_addr71;
        smt_dst_addr72 <= smt_dst_addr71;
        smt_flags72    <= smt_flags71;

        smt_src_addr73 <= smt_src_addr72;
        smt_dst_addr73 <= smt_dst_addr72;
        smt_flags73    <= smt_flags72;

        smt_src_addr74 <= smt_src_addr73;
        smt_dst_addr74 <= smt_dst_addr73;
        smt_flags74    <= smt_flags73;

        smt_src_addr75 <= smt_src_addr74;
        smt_dst_addr75 <= smt_dst_addr74;
        smt_flags75    <= smt_flags74;

        smt_src_addr76 <= smt_src_addr75;
        smt_dst_addr76 <= smt_dst_addr75;
        smt_flags76    <= smt_flags75;

        smt_src_addr77 <= smt_src_addr76;
        smt_dst_addr77 <= smt_dst_addr76;
        smt_flags77    <= smt_flags76;

        smt_src_addr78 <= smt_src_addr77;
        smt_dst_addr78 <= smt_dst_addr77;
        smt_flags78    <= smt_flags77;

        smt_src_addr79 <= smt_src_addr78;
        smt_dst_addr79 <= smt_dst_addr78;
        smt_flags79    <= smt_flags78;

        smt_src_addr80 <= smt_src_addr79;
        smt_dst_addr80 <= smt_dst_addr79;
        smt_flags80    <= smt_flags79;

        smt_src_addr81 <= smt_src_addr80;
        smt_dst_addr81 <= smt_dst_addr80;
        smt_flags81    <= smt_flags80;

        smt_src_addr82 <= smt_src_addr81;
        smt_dst_addr82 <= smt_dst_addr81;
        smt_flags82    <= smt_flags81;

        smt_src_addr83 <= smt_src_addr82;
        smt_dst_addr83 <= smt_dst_addr82;
        smt_flags83    <= smt_flags82;

        smt_src_addr84 <= smt_src_addr83;
        smt_dst_addr84 <= smt_dst_addr83;
        smt_flags84    <= smt_flags83;

        smt_src_addr85 <= smt_src_addr84;
        smt_dst_addr85 <= smt_dst_addr84;
        smt_flags85    <= smt_flags84;

        smt_src_addr86 <= smt_src_addr85;
        smt_dst_addr86 <= smt_dst_addr85;
        smt_flags86    <= smt_flags85;

        smt_src_addr87 <= smt_src_addr86;
        smt_dst_addr87 <= smt_dst_addr86;
        smt_flags87    <= smt_flags86;

        smt_src_addr88 <= smt_src_addr87;
        smt_dst_addr88 <= smt_dst_addr87;
        smt_flags88    <= smt_flags87;

        smt_src_addr89 <= smt_src_addr88;
        smt_dst_addr89 <= smt_dst_addr88;
        smt_flags89    <= smt_flags88;

        smt_src_addr90 <= smt_src_addr89;
        smt_dst_addr90 <= smt_dst_addr89;
        smt_flags90    <= smt_flags89;

        smt_src_addr91 <= smt_src_addr90;
        smt_dst_addr91 <= smt_dst_addr90;
        smt_flags91    <= smt_flags90;

        smt_src_addr92 <= smt_src_addr91;
        smt_dst_addr92 <= smt_dst_addr91;
        smt_flags92    <= smt_flags91;

        smt_src_addr93 <= smt_src_addr92;
        smt_dst_addr93 <= smt_dst_addr92;
        smt_flags93    <= smt_flags92;

        smt_src_addr94 <= smt_src_addr93;
        smt_dst_addr94 <= smt_dst_addr93;
        smt_flags94    <= smt_flags93;

        smt_src_addr95 <= smt_src_addr94;
        smt_dst_addr95 <= smt_dst_addr94;
        smt_flags95    <= smt_flags94;

        smt_src_addr96 <= smt_src_addr95;
        smt_dst_addr96 <= smt_dst_addr95;
        smt_flags96    <= smt_flags95;

        smt_src_addr97 <= smt_src_addr96;
        smt_dst_addr97 <= smt_dst_addr96;
        smt_flags97    <= smt_flags96;

        smt_src_addr98 <= smt_src_addr97;
        smt_dst_addr98 <= smt_dst_addr97;
        smt_flags98    <= smt_flags97;

        smt_src_addr99 <= smt_src_addr98;
        smt_dst_addr99 <= smt_dst_addr98;
        smt_flags99    <= smt_flags98;

        smt_src_addr100 <= smt_src_addr99;
        smt_dst_addr100 <= smt_dst_addr99;
        smt_flags100    <= smt_flags99;

        smt_src_addr101 <= smt_src_addr100;
        smt_dst_addr101 <= smt_dst_addr100;
        smt_flags101    <= smt_flags100;

        smt_src_addr102 <= smt_src_addr101;
        smt_dst_addr102 <= smt_dst_addr101;
        smt_flags102    <= smt_flags101;

        smt_src_addr103 <= smt_src_addr102;
        smt_dst_addr103 <= smt_dst_addr102;
        smt_flags103    <= smt_flags102;

        smt_src_addr104 <= smt_src_addr103;
        smt_dst_addr104 <= smt_dst_addr103;
        smt_flags104    <= smt_flags103;

        smt_src_addr105 <= smt_src_addr104;
        smt_dst_addr105 <= smt_dst_addr104;
        smt_flags105    <= smt_flags104;

        smt_src_addr106 <= smt_src_addr105;
        smt_dst_addr106 <= smt_dst_addr105;
        smt_flags106    <= smt_flags105;

        smt_src_addr107 <= smt_src_addr106;
        smt_dst_addr107 <= smt_dst_addr106;
        smt_flags107    <= smt_flags106;

        smt_src_addr108 <= smt_src_addr107;
        smt_dst_addr108 <= smt_dst_addr107;
        smt_flags108    <= smt_flags107;

        smt_src_addr109 <= smt_src_addr108;
        smt_dst_addr109 <= smt_dst_addr108;
        smt_flags109    <= smt_flags108;

        smt_src_addr110 <= smt_src_addr109;
        smt_dst_addr110 <= smt_dst_addr109;
        smt_flags110    <= smt_flags109;

        smt_src_addr111 <= smt_src_addr110;
        smt_dst_addr111 <= smt_dst_addr110;
        smt_flags111    <= smt_flags110;

        smt_src_addr112 <= smt_src_addr111;
        smt_dst_addr112 <= smt_dst_addr111;
        smt_flags112    <= smt_flags111;

        smt_src_addr113 <= smt_src_addr112;
        smt_dst_addr113 <= smt_dst_addr112;
        smt_flags113    <= smt_flags112;

        smt_src_addr114 <= smt_src_addr113;
        smt_dst_addr114 <= smt_dst_addr113;
        smt_flags114    <= smt_flags113;

        smt_src_addr115 <= smt_src_addr114;
        smt_dst_addr115 <= smt_dst_addr114;
        smt_flags115    <= smt_flags114;

        smt_src_addr116 <= smt_src_addr115;
        smt_dst_addr116 <= smt_dst_addr115;
        smt_flags116    <= smt_flags115;

        smt_src_addr117 <= smt_src_addr116;
        smt_dst_addr117 <= smt_dst_addr116;
        smt_flags117    <= smt_flags116;

        smt_src_addr118 <= smt_src_addr117;
        smt_dst_addr118 <= smt_dst_addr117;
        smt_flags118    <= smt_flags117;

        smt_src_addr119 <= smt_src_addr118;
        smt_dst_addr119 <= smt_dst_addr118;
        smt_flags119    <= smt_flags118;

        smt_src_addr120 <= smt_src_addr119;
        smt_dst_addr120 <= smt_dst_addr119;
        smt_flags120    <= smt_flags119;

        smt_src_addr121 <= smt_src_addr120;
        smt_dst_addr121 <= smt_dst_addr120;
        smt_flags121    <= smt_flags120;

        smt_src_addr122 <= smt_src_addr121;
        smt_dst_addr122 <= smt_dst_addr121;
        smt_flags122    <= smt_flags121;

        smt_src_addr123 <= smt_src_addr122;
        smt_dst_addr123 <= smt_dst_addr122;
        smt_flags123    <= smt_flags122;

        smt_src_addr124 <= smt_src_addr123;
        smt_dst_addr124 <= smt_dst_addr123;
        smt_flags124    <= smt_flags123;

        smt_src_addr125 <= smt_src_addr124;
        smt_dst_addr125 <= smt_dst_addr124;
        smt_flags125    <= smt_flags124;

        smt_src_addr126 <= smt_src_addr125;
        smt_dst_addr126 <= smt_dst_addr125;
        smt_flags126    <= smt_flags125;

        smt_src_addr127 <= smt_src_addr126;
        smt_dst_addr127 <= smt_dst_addr126;
        smt_flags127    <= smt_flags126;

      end

      // register new entry
      //      
      if (smt_cap_2c_rst_r == 1'b1)
        smt_src_addr0  <= ar_pc_save_r;
      else
        smt_src_addr0  <= ca_src_addr;
      smt_dst_addr0  <= ca_dst_addr;
      smt_flags0     <= {1'b1,
                         20'h0,
                         smt_set_rp,
                         ca_int_or_exc_taken | ca_int_epilogue_evt,
                         ca_user_mode_nxt & ~ca_excpn_enter_evt & ~(ca_pass & ca_trap_op_r),
                         8'h0};
    end
  end
end
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
wire                     unused;

// Selecting the stack entry based on the entry and idx fields of the smart
// control aux register
//

wire [1:0]  smt_stack_index;
wire [21:0] smt_stack_ptr;
assign      smt_stack_index = aux_smt_ctrl_r[9:8];
assign      smt_stack_ptr   = aux_smt_ctrl_r[31:10];

always @*
begin : smt_stack_rd_mux1_PROC

  case (smt_stack_ptr) 
    22'd0:
    begin
      smt_stack_src_addr = smt_src_addr0;
      smt_stack_dst_addr = smt_dst_addr0;
      smt_stack_flags    = smt_flags0;
    end

    22'd1:
    begin
      smt_stack_src_addr = smt_src_addr1;
      smt_stack_dst_addr = smt_dst_addr1;
      smt_stack_flags    = smt_flags1;
    end

    22'd2:
    begin
      smt_stack_src_addr = smt_src_addr2;
      smt_stack_dst_addr = smt_dst_addr2;
      smt_stack_flags    = smt_flags2;
    end

    22'd3:
    begin
      smt_stack_src_addr = smt_src_addr3;
      smt_stack_dst_addr = smt_dst_addr3;
      smt_stack_flags    = smt_flags3;
    end

    22'd4:
    begin
      smt_stack_src_addr = smt_src_addr4;
      smt_stack_dst_addr = smt_dst_addr4;
      smt_stack_flags    = smt_flags4;
    end

    22'd5:
    begin
      smt_stack_src_addr = smt_src_addr5;
      smt_stack_dst_addr = smt_dst_addr5;
      smt_stack_flags    = smt_flags5;
    end

    22'd6:
    begin
      smt_stack_src_addr = smt_src_addr6;
      smt_stack_dst_addr = smt_dst_addr6;
      smt_stack_flags    = smt_flags6;
    end

    22'd7:
    begin
      smt_stack_src_addr = smt_src_addr7;
      smt_stack_dst_addr = smt_dst_addr7;
      smt_stack_flags    = smt_flags7;
    end

    22'd8:
    begin
      smt_stack_src_addr = smt_src_addr8;
      smt_stack_dst_addr = smt_dst_addr8;
      smt_stack_flags    = smt_flags8;
    end

    22'd9:
    begin
      smt_stack_src_addr = smt_src_addr9;
      smt_stack_dst_addr = smt_dst_addr9;
      smt_stack_flags    = smt_flags9;
    end

    22'd10:
    begin
      smt_stack_src_addr = smt_src_addr10;
      smt_stack_dst_addr = smt_dst_addr10;
      smt_stack_flags    = smt_flags10;
    end

    22'd11:
    begin
      smt_stack_src_addr = smt_src_addr11;
      smt_stack_dst_addr = smt_dst_addr11;
      smt_stack_flags    = smt_flags11;
    end

    22'd12:
    begin
      smt_stack_src_addr = smt_src_addr12;
      smt_stack_dst_addr = smt_dst_addr12;
      smt_stack_flags    = smt_flags12;
    end

    22'd13:
    begin
      smt_stack_src_addr = smt_src_addr13;
      smt_stack_dst_addr = smt_dst_addr13;
      smt_stack_flags    = smt_flags13;
    end

    22'd14:
    begin
      smt_stack_src_addr = smt_src_addr14;
      smt_stack_dst_addr = smt_dst_addr14;
      smt_stack_flags    = smt_flags14;
    end

    22'd15:
    begin
      smt_stack_src_addr = smt_src_addr15;
      smt_stack_dst_addr = smt_dst_addr15;
      smt_stack_flags    = smt_flags15;
    end

    22'd16:
    begin
      smt_stack_src_addr = smt_src_addr16;
      smt_stack_dst_addr = smt_dst_addr16;
      smt_stack_flags    = smt_flags16;
    end

    22'd17:
    begin
      smt_stack_src_addr = smt_src_addr17;
      smt_stack_dst_addr = smt_dst_addr17;
      smt_stack_flags    = smt_flags17;
    end

    22'd18:
    begin
      smt_stack_src_addr = smt_src_addr18;
      smt_stack_dst_addr = smt_dst_addr18;
      smt_stack_flags    = smt_flags18;
    end

    22'd19:
    begin
      smt_stack_src_addr = smt_src_addr19;
      smt_stack_dst_addr = smt_dst_addr19;
      smt_stack_flags    = smt_flags19;
    end

    22'd20:
    begin
      smt_stack_src_addr = smt_src_addr20;
      smt_stack_dst_addr = smt_dst_addr20;
      smt_stack_flags    = smt_flags20;
    end

    22'd21:
    begin
      smt_stack_src_addr = smt_src_addr21;
      smt_stack_dst_addr = smt_dst_addr21;
      smt_stack_flags    = smt_flags21;
    end

    22'd22:
    begin
      smt_stack_src_addr = smt_src_addr22;
      smt_stack_dst_addr = smt_dst_addr22;
      smt_stack_flags    = smt_flags22;
    end

    22'd23:
    begin
      smt_stack_src_addr = smt_src_addr23;
      smt_stack_dst_addr = smt_dst_addr23;
      smt_stack_flags    = smt_flags23;
    end

    22'd24:
    begin
      smt_stack_src_addr = smt_src_addr24;
      smt_stack_dst_addr = smt_dst_addr24;
      smt_stack_flags    = smt_flags24;
    end

    22'd25:
    begin
      smt_stack_src_addr = smt_src_addr25;
      smt_stack_dst_addr = smt_dst_addr25;
      smt_stack_flags    = smt_flags25;
    end

    22'd26:
    begin
      smt_stack_src_addr = smt_src_addr26;
      smt_stack_dst_addr = smt_dst_addr26;
      smt_stack_flags    = smt_flags26;
    end

    22'd27:
    begin
      smt_stack_src_addr = smt_src_addr27;
      smt_stack_dst_addr = smt_dst_addr27;
      smt_stack_flags    = smt_flags27;
    end

    22'd28:
    begin
      smt_stack_src_addr = smt_src_addr28;
      smt_stack_dst_addr = smt_dst_addr28;
      smt_stack_flags    = smt_flags28;
    end

    22'd29:
    begin
      smt_stack_src_addr = smt_src_addr29;
      smt_stack_dst_addr = smt_dst_addr29;
      smt_stack_flags    = smt_flags29;
    end

    22'd30:
    begin
      smt_stack_src_addr = smt_src_addr30;
      smt_stack_dst_addr = smt_dst_addr30;
      smt_stack_flags    = smt_flags30;
    end

    22'd31:
    begin
      smt_stack_src_addr = smt_src_addr31;
      smt_stack_dst_addr = smt_dst_addr31;
      smt_stack_flags    = smt_flags31;
    end

    22'd32:
    begin
      smt_stack_src_addr = smt_src_addr32;
      smt_stack_dst_addr = smt_dst_addr32;
      smt_stack_flags    = smt_flags32;
    end

    22'd33:
    begin
      smt_stack_src_addr = smt_src_addr33;
      smt_stack_dst_addr = smt_dst_addr33;
      smt_stack_flags    = smt_flags33;
    end

    22'd34:
    begin
      smt_stack_src_addr = smt_src_addr34;
      smt_stack_dst_addr = smt_dst_addr34;
      smt_stack_flags    = smt_flags34;
    end

    22'd35:
    begin
      smt_stack_src_addr = smt_src_addr35;
      smt_stack_dst_addr = smt_dst_addr35;
      smt_stack_flags    = smt_flags35;
    end

    22'd36:
    begin
      smt_stack_src_addr = smt_src_addr36;
      smt_stack_dst_addr = smt_dst_addr36;
      smt_stack_flags    = smt_flags36;
    end

    22'd37:
    begin
      smt_stack_src_addr = smt_src_addr37;
      smt_stack_dst_addr = smt_dst_addr37;
      smt_stack_flags    = smt_flags37;
    end

    22'd38:
    begin
      smt_stack_src_addr = smt_src_addr38;
      smt_stack_dst_addr = smt_dst_addr38;
      smt_stack_flags    = smt_flags38;
    end

    22'd39:
    begin
      smt_stack_src_addr = smt_src_addr39;
      smt_stack_dst_addr = smt_dst_addr39;
      smt_stack_flags    = smt_flags39;
    end

    22'd40:
    begin
      smt_stack_src_addr = smt_src_addr40;
      smt_stack_dst_addr = smt_dst_addr40;
      smt_stack_flags    = smt_flags40;
    end

    22'd41:
    begin
      smt_stack_src_addr = smt_src_addr41;
      smt_stack_dst_addr = smt_dst_addr41;
      smt_stack_flags    = smt_flags41;
    end

    22'd42:
    begin
      smt_stack_src_addr = smt_src_addr42;
      smt_stack_dst_addr = smt_dst_addr42;
      smt_stack_flags    = smt_flags42;
    end

    22'd43:
    begin
      smt_stack_src_addr = smt_src_addr43;
      smt_stack_dst_addr = smt_dst_addr43;
      smt_stack_flags    = smt_flags43;
    end

    22'd44:
    begin
      smt_stack_src_addr = smt_src_addr44;
      smt_stack_dst_addr = smt_dst_addr44;
      smt_stack_flags    = smt_flags44;
    end

    22'd45:
    begin
      smt_stack_src_addr = smt_src_addr45;
      smt_stack_dst_addr = smt_dst_addr45;
      smt_stack_flags    = smt_flags45;
    end

    22'd46:
    begin
      smt_stack_src_addr = smt_src_addr46;
      smt_stack_dst_addr = smt_dst_addr46;
      smt_stack_flags    = smt_flags46;
    end

    22'd47:
    begin
      smt_stack_src_addr = smt_src_addr47;
      smt_stack_dst_addr = smt_dst_addr47;
      smt_stack_flags    = smt_flags47;
    end

    22'd48:
    begin
      smt_stack_src_addr = smt_src_addr48;
      smt_stack_dst_addr = smt_dst_addr48;
      smt_stack_flags    = smt_flags48;
    end

    22'd49:
    begin
      smt_stack_src_addr = smt_src_addr49;
      smt_stack_dst_addr = smt_dst_addr49;
      smt_stack_flags    = smt_flags49;
    end

    22'd50:
    begin
      smt_stack_src_addr = smt_src_addr50;
      smt_stack_dst_addr = smt_dst_addr50;
      smt_stack_flags    = smt_flags50;
    end

    22'd51:
    begin
      smt_stack_src_addr = smt_src_addr51;
      smt_stack_dst_addr = smt_dst_addr51;
      smt_stack_flags    = smt_flags51;
    end

    22'd52:
    begin
      smt_stack_src_addr = smt_src_addr52;
      smt_stack_dst_addr = smt_dst_addr52;
      smt_stack_flags    = smt_flags52;
    end

    22'd53:
    begin
      smt_stack_src_addr = smt_src_addr53;
      smt_stack_dst_addr = smt_dst_addr53;
      smt_stack_flags    = smt_flags53;
    end

    22'd54:
    begin
      smt_stack_src_addr = smt_src_addr54;
      smt_stack_dst_addr = smt_dst_addr54;
      smt_stack_flags    = smt_flags54;
    end

    22'd55:
    begin
      smt_stack_src_addr = smt_src_addr55;
      smt_stack_dst_addr = smt_dst_addr55;
      smt_stack_flags    = smt_flags55;
    end

    22'd56:
    begin
      smt_stack_src_addr = smt_src_addr56;
      smt_stack_dst_addr = smt_dst_addr56;
      smt_stack_flags    = smt_flags56;
    end

    22'd57:
    begin
      smt_stack_src_addr = smt_src_addr57;
      smt_stack_dst_addr = smt_dst_addr57;
      smt_stack_flags    = smt_flags57;
    end

    22'd58:
    begin
      smt_stack_src_addr = smt_src_addr58;
      smt_stack_dst_addr = smt_dst_addr58;
      smt_stack_flags    = smt_flags58;
    end

    22'd59:
    begin
      smt_stack_src_addr = smt_src_addr59;
      smt_stack_dst_addr = smt_dst_addr59;
      smt_stack_flags    = smt_flags59;
    end

    22'd60:
    begin
      smt_stack_src_addr = smt_src_addr60;
      smt_stack_dst_addr = smt_dst_addr60;
      smt_stack_flags    = smt_flags60;
    end

    22'd61:
    begin
      smt_stack_src_addr = smt_src_addr61;
      smt_stack_dst_addr = smt_dst_addr61;
      smt_stack_flags    = smt_flags61;
    end

    22'd62:
    begin
      smt_stack_src_addr = smt_src_addr62;
      smt_stack_dst_addr = smt_dst_addr62;
      smt_stack_flags    = smt_flags62;
    end

    22'd63:
    begin
      smt_stack_src_addr = smt_src_addr63;
      smt_stack_dst_addr = smt_dst_addr63;
      smt_stack_flags    = smt_flags63;
    end

    22'd64:
    begin
      smt_stack_src_addr = smt_src_addr64;
      smt_stack_dst_addr = smt_dst_addr64;
      smt_stack_flags    = smt_flags64;
    end

    22'd65:
    begin
      smt_stack_src_addr = smt_src_addr65;
      smt_stack_dst_addr = smt_dst_addr65;
      smt_stack_flags    = smt_flags65;
    end

    22'd66:
    begin
      smt_stack_src_addr = smt_src_addr66;
      smt_stack_dst_addr = smt_dst_addr66;
      smt_stack_flags    = smt_flags66;
    end

    22'd67:
    begin
      smt_stack_src_addr = smt_src_addr67;
      smt_stack_dst_addr = smt_dst_addr67;
      smt_stack_flags    = smt_flags67;
    end

    22'd68:
    begin
      smt_stack_src_addr = smt_src_addr68;
      smt_stack_dst_addr = smt_dst_addr68;
      smt_stack_flags    = smt_flags68;
    end

    22'd69:
    begin
      smt_stack_src_addr = smt_src_addr69;
      smt_stack_dst_addr = smt_dst_addr69;
      smt_stack_flags    = smt_flags69;
    end

    22'd70:
    begin
      smt_stack_src_addr = smt_src_addr70;
      smt_stack_dst_addr = smt_dst_addr70;
      smt_stack_flags    = smt_flags70;
    end

    22'd71:
    begin
      smt_stack_src_addr = smt_src_addr71;
      smt_stack_dst_addr = smt_dst_addr71;
      smt_stack_flags    = smt_flags71;
    end

    22'd72:
    begin
      smt_stack_src_addr = smt_src_addr72;
      smt_stack_dst_addr = smt_dst_addr72;
      smt_stack_flags    = smt_flags72;
    end

    22'd73:
    begin
      smt_stack_src_addr = smt_src_addr73;
      smt_stack_dst_addr = smt_dst_addr73;
      smt_stack_flags    = smt_flags73;
    end

    22'd74:
    begin
      smt_stack_src_addr = smt_src_addr74;
      smt_stack_dst_addr = smt_dst_addr74;
      smt_stack_flags    = smt_flags74;
    end

    22'd75:
    begin
      smt_stack_src_addr = smt_src_addr75;
      smt_stack_dst_addr = smt_dst_addr75;
      smt_stack_flags    = smt_flags75;
    end

    22'd76:
    begin
      smt_stack_src_addr = smt_src_addr76;
      smt_stack_dst_addr = smt_dst_addr76;
      smt_stack_flags    = smt_flags76;
    end

    22'd77:
    begin
      smt_stack_src_addr = smt_src_addr77;
      smt_stack_dst_addr = smt_dst_addr77;
      smt_stack_flags    = smt_flags77;
    end

    22'd78:
    begin
      smt_stack_src_addr = smt_src_addr78;
      smt_stack_dst_addr = smt_dst_addr78;
      smt_stack_flags    = smt_flags78;
    end

    22'd79:
    begin
      smt_stack_src_addr = smt_src_addr79;
      smt_stack_dst_addr = smt_dst_addr79;
      smt_stack_flags    = smt_flags79;
    end

    22'd80:
    begin
      smt_stack_src_addr = smt_src_addr80;
      smt_stack_dst_addr = smt_dst_addr80;
      smt_stack_flags    = smt_flags80;
    end

    22'd81:
    begin
      smt_stack_src_addr = smt_src_addr81;
      smt_stack_dst_addr = smt_dst_addr81;
      smt_stack_flags    = smt_flags81;
    end

    22'd82:
    begin
      smt_stack_src_addr = smt_src_addr82;
      smt_stack_dst_addr = smt_dst_addr82;
      smt_stack_flags    = smt_flags82;
    end

    22'd83:
    begin
      smt_stack_src_addr = smt_src_addr83;
      smt_stack_dst_addr = smt_dst_addr83;
      smt_stack_flags    = smt_flags83;
    end

    22'd84:
    begin
      smt_stack_src_addr = smt_src_addr84;
      smt_stack_dst_addr = smt_dst_addr84;
      smt_stack_flags    = smt_flags84;
    end

    22'd85:
    begin
      smt_stack_src_addr = smt_src_addr85;
      smt_stack_dst_addr = smt_dst_addr85;
      smt_stack_flags    = smt_flags85;
    end

    22'd86:
    begin
      smt_stack_src_addr = smt_src_addr86;
      smt_stack_dst_addr = smt_dst_addr86;
      smt_stack_flags    = smt_flags86;
    end

    22'd87:
    begin
      smt_stack_src_addr = smt_src_addr87;
      smt_stack_dst_addr = smt_dst_addr87;
      smt_stack_flags    = smt_flags87;
    end

    22'd88:
    begin
      smt_stack_src_addr = smt_src_addr88;
      smt_stack_dst_addr = smt_dst_addr88;
      smt_stack_flags    = smt_flags88;
    end

    22'd89:
    begin
      smt_stack_src_addr = smt_src_addr89;
      smt_stack_dst_addr = smt_dst_addr89;
      smt_stack_flags    = smt_flags89;
    end

    22'd90:
    begin
      smt_stack_src_addr = smt_src_addr90;
      smt_stack_dst_addr = smt_dst_addr90;
      smt_stack_flags    = smt_flags90;
    end

    22'd91:
    begin
      smt_stack_src_addr = smt_src_addr91;
      smt_stack_dst_addr = smt_dst_addr91;
      smt_stack_flags    = smt_flags91;
    end

    22'd92:
    begin
      smt_stack_src_addr = smt_src_addr92;
      smt_stack_dst_addr = smt_dst_addr92;
      smt_stack_flags    = smt_flags92;
    end

    22'd93:
    begin
      smt_stack_src_addr = smt_src_addr93;
      smt_stack_dst_addr = smt_dst_addr93;
      smt_stack_flags    = smt_flags93;
    end

    22'd94:
    begin
      smt_stack_src_addr = smt_src_addr94;
      smt_stack_dst_addr = smt_dst_addr94;
      smt_stack_flags    = smt_flags94;
    end

    22'd95:
    begin
      smt_stack_src_addr = smt_src_addr95;
      smt_stack_dst_addr = smt_dst_addr95;
      smt_stack_flags    = smt_flags95;
    end

    22'd96:
    begin
      smt_stack_src_addr = smt_src_addr96;
      smt_stack_dst_addr = smt_dst_addr96;
      smt_stack_flags    = smt_flags96;
    end

    22'd97:
    begin
      smt_stack_src_addr = smt_src_addr97;
      smt_stack_dst_addr = smt_dst_addr97;
      smt_stack_flags    = smt_flags97;
    end

    22'd98:
    begin
      smt_stack_src_addr = smt_src_addr98;
      smt_stack_dst_addr = smt_dst_addr98;
      smt_stack_flags    = smt_flags98;
    end

    22'd99:
    begin
      smt_stack_src_addr = smt_src_addr99;
      smt_stack_dst_addr = smt_dst_addr99;
      smt_stack_flags    = smt_flags99;
    end

    22'd100:
    begin
      smt_stack_src_addr = smt_src_addr100;
      smt_stack_dst_addr = smt_dst_addr100;
      smt_stack_flags    = smt_flags100;
    end

    22'd101:
    begin
      smt_stack_src_addr = smt_src_addr101;
      smt_stack_dst_addr = smt_dst_addr101;
      smt_stack_flags    = smt_flags101;
    end

    22'd102:
    begin
      smt_stack_src_addr = smt_src_addr102;
      smt_stack_dst_addr = smt_dst_addr102;
      smt_stack_flags    = smt_flags102;
    end

    22'd103:
    begin
      smt_stack_src_addr = smt_src_addr103;
      smt_stack_dst_addr = smt_dst_addr103;
      smt_stack_flags    = smt_flags103;
    end

    22'd104:
    begin
      smt_stack_src_addr = smt_src_addr104;
      smt_stack_dst_addr = smt_dst_addr104;
      smt_stack_flags    = smt_flags104;
    end

    22'd105:
    begin
      smt_stack_src_addr = smt_src_addr105;
      smt_stack_dst_addr = smt_dst_addr105;
      smt_stack_flags    = smt_flags105;
    end

    22'd106:
    begin
      smt_stack_src_addr = smt_src_addr106;
      smt_stack_dst_addr = smt_dst_addr106;
      smt_stack_flags    = smt_flags106;
    end

    22'd107:
    begin
      smt_stack_src_addr = smt_src_addr107;
      smt_stack_dst_addr = smt_dst_addr107;
      smt_stack_flags    = smt_flags107;
    end

    22'd108:
    begin
      smt_stack_src_addr = smt_src_addr108;
      smt_stack_dst_addr = smt_dst_addr108;
      smt_stack_flags    = smt_flags108;
    end

    22'd109:
    begin
      smt_stack_src_addr = smt_src_addr109;
      smt_stack_dst_addr = smt_dst_addr109;
      smt_stack_flags    = smt_flags109;
    end

    22'd110:
    begin
      smt_stack_src_addr = smt_src_addr110;
      smt_stack_dst_addr = smt_dst_addr110;
      smt_stack_flags    = smt_flags110;
    end

    22'd111:
    begin
      smt_stack_src_addr = smt_src_addr111;
      smt_stack_dst_addr = smt_dst_addr111;
      smt_stack_flags    = smt_flags111;
    end

    22'd112:
    begin
      smt_stack_src_addr = smt_src_addr112;
      smt_stack_dst_addr = smt_dst_addr112;
      smt_stack_flags    = smt_flags112;
    end

    22'd113:
    begin
      smt_stack_src_addr = smt_src_addr113;
      smt_stack_dst_addr = smt_dst_addr113;
      smt_stack_flags    = smt_flags113;
    end

    22'd114:
    begin
      smt_stack_src_addr = smt_src_addr114;
      smt_stack_dst_addr = smt_dst_addr114;
      smt_stack_flags    = smt_flags114;
    end

    22'd115:
    begin
      smt_stack_src_addr = smt_src_addr115;
      smt_stack_dst_addr = smt_dst_addr115;
      smt_stack_flags    = smt_flags115;
    end

    22'd116:
    begin
      smt_stack_src_addr = smt_src_addr116;
      smt_stack_dst_addr = smt_dst_addr116;
      smt_stack_flags    = smt_flags116;
    end

    22'd117:
    begin
      smt_stack_src_addr = smt_src_addr117;
      smt_stack_dst_addr = smt_dst_addr117;
      smt_stack_flags    = smt_flags117;
    end

    22'd118:
    begin
      smt_stack_src_addr = smt_src_addr118;
      smt_stack_dst_addr = smt_dst_addr118;
      smt_stack_flags    = smt_flags118;
    end

    22'd119:
    begin
      smt_stack_src_addr = smt_src_addr119;
      smt_stack_dst_addr = smt_dst_addr119;
      smt_stack_flags    = smt_flags119;
    end

    22'd120:
    begin
      smt_stack_src_addr = smt_src_addr120;
      smt_stack_dst_addr = smt_dst_addr120;
      smt_stack_flags    = smt_flags120;
    end

    22'd121:
    begin
      smt_stack_src_addr = smt_src_addr121;
      smt_stack_dst_addr = smt_dst_addr121;
      smt_stack_flags    = smt_flags121;
    end

    22'd122:
    begin
      smt_stack_src_addr = smt_src_addr122;
      smt_stack_dst_addr = smt_dst_addr122;
      smt_stack_flags    = smt_flags122;
    end

    22'd123:
    begin
      smt_stack_src_addr = smt_src_addr123;
      smt_stack_dst_addr = smt_dst_addr123;
      smt_stack_flags    = smt_flags123;
    end

    22'd124:
    begin
      smt_stack_src_addr = smt_src_addr124;
      smt_stack_dst_addr = smt_dst_addr124;
      smt_stack_flags    = smt_flags124;
    end

    22'd125:
    begin
      smt_stack_src_addr = smt_src_addr125;
      smt_stack_dst_addr = smt_dst_addr125;
      smt_stack_flags    = smt_flags125;
    end

    22'd126:
    begin
      smt_stack_src_addr = smt_src_addr126;
      smt_stack_dst_addr = smt_dst_addr126;
      smt_stack_flags    = smt_flags126;
    end

    22'd127:
    begin
      smt_stack_src_addr = smt_src_addr127;
      smt_stack_dst_addr = smt_dst_addr127;
      smt_stack_flags    = smt_flags127;
    end

    default:
    begin
      smt_stack_src_addr = `npuarc_PC_BITS'h0;
      smt_stack_dst_addr = `npuarc_PC_BITS'h0;
      smt_stack_flags    = `npuarc_DATA_SIZE'h0;
    end
  endcase

end    // smt_stack_rd_mux1_PROC


always @*
begin : smt_stack_rd_mux2_PROC
  smt_stack_data = `npuarc_DATA_SIZE'h0;
  case (smt_stack_index) 
  2'b00:   smt_stack_data = {smt_stack_src_addr, 1'b0};
  2'b01:   smt_stack_data = {smt_stack_dst_addr, 1'b0};
  2'b10:   smt_stack_data = smt_stack_flags;
  default: smt_stack_data = `npuarc_DATA_SIZE'h0;
  endcase

end    // smt_stack_rd_mux2_PROC


assign smt_unit_enable  = aux_smt_active
                        | aux_smt_ctrl_r[0]
                        | smt_cap_rst_vec
                        ;

assign   smt_en = aux_smt_ctrl_r[0];

endmodule // alb_smart_unified
// spyglass enable_block OneModule-ML
