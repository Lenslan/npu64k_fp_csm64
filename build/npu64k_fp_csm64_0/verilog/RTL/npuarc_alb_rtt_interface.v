// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
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
// ######  ####### #######
// #     #    #       #
// #     #    #       #
// #    #     #       #
// ######     #       #
// #    #     #       #
// #     #    #       #
//
// ============================================================================
//
// Description:
//
//  This module implements the configurable Real-Time Trace (RTT) unit for HS.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_rtt_interface.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

`define SV_DEBUG_ON 0

module npuarc_alb_rtt_interface (

  ////////// Interface for Safety ///////////////

//`if (`RTT_EXT_TRACE_IF_CLIENT == 1) // {
//  output reg                  rtt_aux_stall,
//  output reg                  rtt_if_active,
//`endif  // }
  ////////// Interface for SR instructions to write aux regs ///////////////
  //         (WA stage)
  input                       aux_rtt_wen_r,    // (WA) Aux write enable
  input       [3:0]           aux_rtt_waddr_r,  // (WA) Aux write Address
  input       [`npuarc_DATA_RANGE]   wa_sr_data_r,     // (WA) Aux write data

  ////////// Interface for aux address / perm checks and aux read //////////
  //         (X3 stage)
  input                       aux_write,        // (X3) Aux write operation
  input                       aux_read,         // (X3) Aux read operation
  input                       aux_rtt_ren_r,    // (X3) Aux unit select
  input       [3:0]           aux_rtt_raddr_r,  // (X3) Aux address (rd/wr)

  output reg  [`npuarc_DATA_RANGE]   rtt_aux_rdata,    // (X3) LR read data
  output reg                  rtt_aux_illegal,  // (X3) SR/LR op is illegal
  output reg                  rtt_aux_k_rd,     // (X3) op needs Kernel R perm
  output reg                  rtt_aux_k_wr,     // (X3) op needs Kernel W perm
  output reg                  rtt_aux_unimpl,   // (X3) LR/SR reg is not present
  output reg                  rtt_aux_serial_sr,// (X3) SR group flush
  output reg                  rtt_aux_strict_sr,// (X3) SR single flush

  input [`npuarc_MMU_PID_ASID_RANGE] asid_r,           // Current pid.asid
  input                       asid_wr_en,       // pid.asid changed (by aux wr)

  ////////// Pipeline interface /////////////////////////////////////////
  //
  input                       ca_pass,

  input       [`npuarc_PC_RANGE]     ar_pc_r,
  input       [`npuarc_PC_RANGE]     ar_pc_nxt,
  input [21:0]                intvbase_in, // for external vector base config

  input                       ca_excpn_prol_evt,
  input                       ca_excpn_enter_evt,

  input                       ca_int_enter_evt,

  ////////// Pipeline tracking inputs  ///////////////////////////////////
  //
  input                       commit_normal_evt,
  input                       ca_cond_inst,
  input                       ca_cond_met,
  input                       ca_br_or_jmp_all,
  input                       ca_indir_br,
  input                       ca_dslot_r,
  input                       ca_in_deslot,
  input                       ca_in_eslot_r,
  input                       rtt_leave_uop_cmt,
  input                       ca_zol_lp_jmp,
  input                       ca_cmt_brk_inst,
  input                       ca_cmt_isi_evt,
  input                       dbg_halt_r,   // debug halt
  input [`npuarc_DATA_RANGE]         ar_aux_ecr_r,

  output reg                  da_rtt_stall_r, // stall execution

  input                       dbg_ra_r,
  input                       dbg_bh_r,     // break halt
// spyglass disable_block W240
// SMD: inputs declared but not read
// SJ:  kept for debug interface
  input                       dbg_sh_r,     // self_halt
  input                       dbg_eh_r,     // external halt (cur unused)
// spyglass enable_block W240
  input                       dbg_ah_r,     // actionpoint halt

  input                       gb_sys_sleep_r,
  input                       gb_sys_halt_r,

// spyglass disable_block W240
// SMD: inputs declared but not read
// SJ:  aps_1_active unused but kept for interface
  input      [`npuarc_APNUM_RANGE]   aps_active,      // Identity of active hit
// spyglass enable_block W240
  input                       aps_halt,    // Halt due to AP match
  input                       aps_break,   // Break due to AP match
  input     [`npuarc_APS_RANGE]      aps_status,       // All triggered Actionpoints
  input                       aps_excpn,        // Excpn due to AP match
  input                       ap_tkn,

  // AUX register read/write monitoring
// spyglass disable_block W240
// SMD: inputs declared but not read
// SJ:  kept for aux interface
  input                       wa_lr_op_r,
  input                       wa_sr_op_r,
  input  [`npuarc_AUX_REG_RANGE]     wa_aux_addr_r,
// spyglass enable_block W240
  // Core register write monitoring
// spyglass disable_block W240
// SMD: inputs declared but not read
// SJ:  kept for core reg write monitering interface
  input  [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa0_r,
  input                       wa_rf_wenb0_r,
  input  [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa1_r,
  input                       wa_rf_wenb1_r,

  input  [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r, //mon auxRd, aluOp (coreWr)
  input  [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r, //mon memRd, eiaOp, fpuOp

  input  [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_r,
  input                       wa_rf_wenb0_64_r,
  input  [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_r,
  input                       wa_rf_wenb1_64_r,

// spyglass enable_block W240



  //  RTT External Pins

  ////////// RTT Programming interface ///////////////////////////////////
  //
  output reg                rtt_read_a,  // RTT read pulse
  output reg                rtt_write_a, // RTT write pulse
  output [`npuarc_RTT_ADDR_RANGE]  rtt_addr_r,  // RTT Pgm Address
  input  [`npuarc_DATA_RANGE]      rtt_drd_r,   // RTT read data
  output [`npuarc_DATA_RANGE]      rtt_dwr_r,   // RTT write data

  ///////// RTT Pipeline tracking outputs ////////////////////////////////
  //
  output reg          rtt_inst_commit,   // instruction has committed
  output [`npuarc_PC_RANGE]  rtt_inst_addr,     // instruction address (pc)
  output reg          rtt_cond_valid,    // commit inst was conditional
  output reg          rtt_cond_pass,     // condition code test passed

  output reg          rtt_branch,        // instruction was a branch
  output reg          rtt_branch_indir,  // branch was indirect
  output reg [`npuarc_PC_RANGE] rtt_branch_taddr, // Target address of branch/exc
  output reg          rtt_dslot,         // Branch has delay slot
  output reg          rtt_in_deslot,     // in d or e slot
  output reg          rtt_in_eslot,      // in e slot
  output reg          rtt_uop_is_leave,  // ca has leave_s gen'd uop instr
  output reg          rtt_exception,     // exception has been taken
  input               excpn_exit_evt,
  output reg          rtt_exception_rtn, // exception exit
  output reg          rtt_interrupt,     // interrupt has been taken
  output reg          rtt_zd_loop,       // zero-delay loop has been taken

  // always '0' in HS
  output    [7:0]     rtt_process_id,    // Current value of PID register
  output reg          rtt_pid_wr_en,     // Write enable for PID register

  output reg          rtt_ss_halt,
  output reg          rtt_sw_bp,         // software breakpoint hit
  output              rtt_hw_bp,         // hardware breakpoint hit
  output              rtt_hw_exc,        // hardware error (memory error)
  output              rtt_sleep_mode,
  output              rtt_dbg_halt,
  output              rtt_rst_applied,

  // Actionpoints
  output              rtt_wp_hit,        // actionpoint has been hit
  output    [7:0]     rtt_wp_val,        // which actionpoints triggered


  ////////// Interface for SR instructions to SW aux regs ///////////////
  output reg  [32:0]   rtt_swe_data,    // SW Trace data to RTT
  output reg           rtt_swe_val,     // SW Trace data valid to RTT

  // freeze CPU (RTT fifo's almost full)
  input               rtt_freeze,        // freeze (stall) CPU pipeline


  ////////// General input signals /////////////////////////////////////////
  //
  input               clk,               // clock
  input               rst_a              // asynchronous reset

);

// Local declarations

wire                   ca_inst_commit;

wire [`npuarc_AUX_REG_RANGE]  AUX_ADDR_RTT_ADDR = `npuarc_RTT_ADDR_AUX;
wire [`npuarc_AUX_REG_RANGE]  AUX_ADDR_RTT_DATA = `npuarc_RTT_DATA_AUX;
wire [`npuarc_AUX_REG_RANGE]  AUX_ADDR_RTT_CTRL = `npuarc_RTT_CTRL_AUX;
wire [`npuarc_AUX_REG_RANGE]  AUX_ADDR_RTT_SWE0 = `npuarc_RTT_SWE0_AUX;
wire [`npuarc_AUX_REG_RANGE]  AUX_ADDR_RTT_SWE1 = `npuarc_RTT_SWE1_AUX;

reg                    rtt_read_nxt;
reg                    rtt_write_nxt;
reg                    aux_rtt_addr_wen;
reg                    aux_rtt_data_wen;

reg                    aux_rtt_swe0_wen;
reg                    aux_rtt_swe1_wen;


reg  [`npuarc_RTT_ADDR_RANGE] aux_rtt_addr_r;
reg  [`npuarc_DATA_RANGE]     aux_rtt_data_r;

reg  [`npuarc_DATA_RANGE]     aux_rtt_swe0_r;
reg  [`npuarc_DATA_RANGE]     aux_rtt_swe1_r;

reg                    cycle1;

// PC that takes care of providing vector location during exceptions
reg [`npuarc_PC_RANGE]        rtt_pc_r;
wire                   commit_normal_evt_0;


assign commit_normal_evt_0 = commit_normal_evt;

// Latching instruction location during exception
// - otherwise reflects arch PC
always @(posedge clk or posedge rst_a)
begin : rtt_pc_r_PROC
  if (rst_a == 1'b1)
  begin
    rtt_pc_r   <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    cycle1     <= 1'b1;
  end
  else
  begin
// This is needed because tools do not accept variable reset values.
    if (cycle1)
    begin
      rtt_pc_r <= {intvbase_in, 9'b0};
      cycle1   <= 1'b0;
    end
    else
    if (ca_inst_commit | ca_excpn_prol_evt)
    begin
// spyglass disable_block Ac_glitch04 Ac_unsync02 Reset_sync04
// SMD: glitches possible due to unsyc crossings
// SJ:  no logical dependencies to mcip domain
      rtt_pc_r <= ar_pc_r;
// spyglass enable_block Ac_glitch04 Ac_unsync02 Reset_sync04
    end
  end
end

// current PC (address of committing instruction)
assign rtt_inst_addr = rtt_pc_r;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Auxiliary registers, next state, read mux and write enable logic       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// X3 stage (eval rd/wr/perm, perform read)
//
always @*
begin : smart_rtt_rdwr_PROC

  rtt_aux_rdata       = `npuarc_DATA_SIZE'd0;
  rtt_aux_k_rd        = 1'b0;
  rtt_aux_k_wr        = 1'b0;
  rtt_aux_unimpl      = 1'b1;
  rtt_aux_illegal     = 1'b0;
  rtt_aux_serial_sr   = 1'b0;
  rtt_aux_strict_sr   = 1'b0;

  if (aux_rtt_ren_r)  // rtt aux region selected
  begin

    case (aux_rtt_raddr_r)

    AUX_ADDR_RTT_CTRL[3:0]: // K_WRITE
    begin
      rtt_aux_illegal = aux_read;
      rtt_aux_k_wr    = 1'b1;
      rtt_aux_unimpl    = 1'b0;
      rtt_aux_strict_sr = aux_write; // ctrl wr is serializing
    end

    AUX_ADDR_RTT_ADDR[3:0]: // K_RW
    begin
      rtt_aux_rdata[`npuarc_RTT_ADDR_RANGE] = aux_rtt_addr_r;
      rtt_aux_k_rd    = 1'b1;
      rtt_aux_k_wr    = 1'b1;
      rtt_aux_unimpl    = 1'b0;
      rtt_aux_strict_sr = aux_write; // addr wr is serializing
    end

    AUX_ADDR_RTT_DATA[3:0]: // K_RW
    begin
      rtt_aux_rdata   = aux_rtt_data_r;
      rtt_aux_k_rd    = 1'b1;
      rtt_aux_k_wr    = 1'b1;
      rtt_aux_unimpl  = 1'b0;
    end


    AUX_ADDR_RTT_SWE0[3:0]: // ANY_RW
    begin
      rtt_aux_rdata   = aux_rtt_swe0_r;
      rtt_aux_k_rd    = 1'b0;
      rtt_aux_k_wr    = 1'b0;
      rtt_aux_unimpl  = 1'b0;
      rtt_aux_strict_sr = 1'b0; // swe is non-serializing
    end
    AUX_ADDR_RTT_SWE1[3:0]: // ANY_RW
    begin
      rtt_aux_rdata   = aux_rtt_swe1_r;
      rtt_aux_k_rd    = 1'b0;
      rtt_aux_k_wr    = 1'b0;
      rtt_aux_unimpl  = 1'b0;
      rtt_aux_strict_sr = 1'b0; // swe is non-serializing
    end

    default:
    begin
      // aux_addr is not implemented in this module
      // (already in default assigns, kept for lint)
      rtt_aux_unimpl   = 1'b1;
    end
    endcase
  end

end // block: smart_reg_rd_PROC

// AUX write logic : WA stage (perform write)
//
always @*
begin : rtt_reg_wr_PROC

  rtt_read_nxt        = 1'b0;
  rtt_write_nxt       = 1'b0;
  aux_rtt_addr_wen    = 1'b0;
  aux_rtt_data_wen    = 1'b0;
  aux_rtt_swe0_wen    = 1'b0;
  aux_rtt_swe1_wen    = 1'b0;

  if (aux_rtt_wen_r)
  begin

    case (aux_rtt_waddr_r)
    AUX_ADDR_RTT_CTRL[3:0]: // K_WRITE
    begin
      rtt_read_nxt    = !wa_sr_data_r[0];
      rtt_write_nxt   =  wa_sr_data_r[0];
    end

    AUX_ADDR_RTT_ADDR[3:0]: // K_RW
    begin
      aux_rtt_addr_wen = 1'b1;
    end

    AUX_ADDR_RTT_DATA[3:0]: // K_RW
    begin
      aux_rtt_data_wen = 1'b1;
    end


    AUX_ADDR_RTT_SWE0[3:0]: // ANY_RW
    begin
      aux_rtt_swe0_wen = 1'b1;
    end
    AUX_ADDR_RTT_SWE1[3:0]: // ANY_RW
    begin
      aux_rtt_swe1_wen = 1'b1;
    end

    default:
    begin
      // (already in default assigns, kept for lint)
      rtt_write_nxt = 1'b0;
    end
    endcase
  end

end // block: rtt_reg_wr_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining RTT auxiliary registers: addr, data         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign rtt_addr_r = aux_rtt_addr_r;
assign rtt_dwr_r  = aux_rtt_data_r;

always @(posedge clk or posedge rst_a)
begin : rtt_pgm_ifc_regs_PROC
  if (rst_a == 1'b1)
  begin
    aux_rtt_addr_r      <= {`npuarc_RTT_ADDR_BITS{1'b0}};
    aux_rtt_data_r      <= {`npuarc_DATA_SIZE{1'b0}};
    rtt_read_a          <= 1'b0;
    rtt_write_a         <= 1'b0;
    aux_rtt_swe0_r      <= {`npuarc_DATA_SIZE{1'b0}};
    aux_rtt_swe1_r      <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else
  begin

    if (aux_rtt_addr_wen)          // aux write of addr reg
    begin
      aux_rtt_addr_r <= wa_sr_data_r[`npuarc_RTT_ADDR_RANGE];
    end

    if (aux_rtt_swe0_wen)          // aux write of swe0 reg
    begin
      aux_rtt_swe0_r <= wa_sr_data_r;
    end
    if (aux_rtt_swe1_wen)          // aux write of swe1 reg
    begin
      aux_rtt_swe1_r <= wa_sr_data_r;
    end
    if (aux_rtt_data_wen)          // aux write of data reg
    begin
      aux_rtt_data_r <= wa_sr_data_r;
    end
    else
    if (rtt_read_a)                // capture rd data from ext pins
    begin
      aux_rtt_data_r <= rtt_drd_r;
    end

    // generate rd/wr pulses to RTT programming interface
    rtt_read_a  <= rtt_read_nxt;
    rtt_write_a <= rtt_write_nxt;

  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Pipeline / Instruction Tracking                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
assign ca_inst_commit = commit_normal_evt & (~ca_excpn_enter_evt);

always @(posedge clk or posedge rst_a)
begin:  wa_rtt_pgm_trace_PROC
  if (rst_a == 1'b1)
  begin
    rtt_inst_commit         <= 1'b0;
    rtt_cond_valid          <= 1'b0;
    rtt_cond_pass           <= 1'b0;
    rtt_branch_taddr        <= `npuarc_PC_BITS'd0;
    rtt_branch              <= 1'b0;
    rtt_branch_indir        <= 1'b0;
    rtt_dslot               <= 1'b0;
    rtt_in_deslot           <= 1'b0;
    rtt_in_eslot            <= 1'b0;
    rtt_uop_is_leave        <= 1'b0;
    rtt_exception           <= 1'b0;
    rtt_exception_rtn       <= 1'b0;
    rtt_interrupt           <= 1'b0;
    rtt_zd_loop             <= 1'b0;
    rtt_ss_halt             <= 1'b0;
    rtt_sw_bp               <= 1'b0;
  end
  else
  begin

    // Commit any inst except uop internal or debug inst
    rtt_inst_commit  <= commit_normal_evt_0 & (~ca_excpn_enter_evt);
    // committing instruction is conditional
    rtt_cond_valid   <= ca_cond_inst & ca_inst_commit;
    // predicate/condition satisfied (inst will commit)
    rtt_cond_pass     <= ca_cond_met & ca_inst_commit;
    // indicates any branch or jump (taken or not taken)
    rtt_branch        <= ca_br_or_jmp_all & ca_inst_commit;
    rtt_branch_indir  <= ca_indir_br & ca_inst_commit;

    // next pc (address of next inst; seq/branchTarget/excpnVector)
    rtt_branch_taddr  <= ar_pc_nxt;

    // branch has dslot, assert at branch commit (not in_dslot)
    rtt_dslot         <= ca_dslot_r & ca_pass & (~ca_excpn_enter_evt);

    // ca stage has d or e slot inst commiting
    rtt_in_deslot     <= ca_in_deslot & ca_pass & (~ca_excpn_enter_evt);

    // ca stage has e slot inst commiting (instruction executed by EI_S)
    rtt_in_eslot      <= ca_in_eslot_r & ca_pass & (~ca_excpn_enter_evt);

    // ca stage has leave_s generated uop instr
    rtt_uop_is_leave  <= rtt_leave_uop_cmt & ca_pass & (~ca_excpn_enter_evt);

    // assert when exiting prologue (all exceptions, incl swi/trap)
    rtt_exception     <= ca_excpn_enter_evt;

    // RTIE is being executed
    rtt_exception_rtn <= excpn_exit_evt;

    // completion of interrupt prologue; implicit branch from vector
    // address to entry point of handler
    rtt_interrupt    <= ca_int_enter_evt;

    // loop implicit jump from loop end to loop start
    rtt_zd_loop       <= ca_zol_lp_jmp & (~ca_excpn_enter_evt) & (~ca_excpn_prol_evt);


    // Single-step halt (pulse)
    rtt_ss_halt       <= ca_cmt_isi_evt;

    // Software break point - brk inst commit (pulse)
    rtt_sw_bp         <= ca_cmt_brk_inst;

  end // else: !if(rst_a == 1'b1)
end // block: wa_rtt_pgm_trace_PROC


//////////////////////////////////////////////////////////////////////////////
// HALT / RUN / Reset status bits
//

// Halt due to debug host (level)
assign rtt_dbg_halt     =  gb_sys_halt_r       // cpu halted
                        & (  dbg_halt_r        // debug halt
                           | dbg_ah_r          // actionpoint halt
                           | dbg_bh_r          // break halt (brk)
                          )
                        ;


// Memory error (bus error / internal memory error)
assign rtt_hw_exc  = ca_excpn_enter_evt
                   & (  (ar_aux_ecr_r[`npuarc_ECR_VEC_RANGE] == 8'h1)
                      | (ar_aux_ecr_r[`npuarc_ECR_VEC_RANGE] == 8'h3)
                     );

// Sleep mode (needed? in addition to enter sleep, pulse)
assign rtt_sleep_mode   = gb_sys_sleep_r;

// Reset applied status
assign rtt_rst_applied  = dbg_ra_r;


//////////////////////////////////////////////////////////////////////////////
// actionpoint hits

// Exception due to Actionpoint / Watchpoint
assign rtt_wp_hit       = aps_excpn & ca_excpn_prol_evt;
// Halt due to Actionpoint / Watchpoint
assign rtt_hw_bp        = (1'b0
                        | aps_break | aps_halt
                        ) & (1'b0
                        | ap_tkn
                        )
                        ;

assign rtt_wp_val       = aps_status;       // cumulative hits (one hot)


// pid reg when mmu present
assign rtt_process_id   = asid_r;

always @(posedge clk or posedge rst_a)
begin: rtt_pid_wr_en_PROC
  if (rst_a == 1'b1)
  begin
    rtt_pid_wr_en <= 1'b0;
  end
  else
  begin
    rtt_pid_wr_en <= asid_wr_en;
  end
end


assign rtt_freeze_en = 1'b1;

always @(posedge clk or posedge rst_a)
begin:  da_rtt_stall_PROC
  if (rst_a == 1'b1)
  begin
    da_rtt_stall_r <= 1'b0;
  end
  else
  begin
    da_rtt_stall_r <= rtt_freeze & rtt_freeze_en;
  end
end

always @(posedge clk or posedge rst_a)
begin : RTT_SW_DATA_PROC
  if (rst_a == 1'b1)
  begin
    rtt_swe_data  <= 33'b0;
  end
  else if (aux_rtt_swe1_wen || aux_rtt_swe0_wen)
    begin
      rtt_swe_data  <= {aux_rtt_swe1_wen,wa_sr_data_r};
    end
end

always @(posedge clk or posedge rst_a)
begin : RTT_SW_VAL_PROC
  if (rst_a == 1'b1)
    begin
      rtt_swe_val  <= 1'b0;
    end
  else
    begin
      rtt_swe_val  <= (aux_rtt_swe1_wen || aux_rtt_swe0_wen);
    end
end


endmodule // RTT

