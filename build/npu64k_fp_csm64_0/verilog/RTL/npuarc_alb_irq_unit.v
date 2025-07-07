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
// ###  ######    #####          #     #  #     #  ###  #######
//  #   #     #  #     #         #     #  ##    #   #      #
//  #   #     #  #     #         #     #  # #   #   #      #
//  #   ######   #     #         #     #  #  #  #   #      #
//  #   #   #    #   # #         #     #  #   # #   #      #
//  #   #    #   #    #          #     #  #    ##   #      #
// ###  #     #   #### #  #####   #####   #     #  ###     #
//
// ===========================================================================
//
// Description:
//
//  This module implements the configurable interrupt unit of the ARCv2HS CPU.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_irq_unit (

  ////////// Interface for LR/SR instructions to access aux regs /////////////////
  //
  input                       aux_read,          // AUX is for read
  input                       aux_write,         // AUX is for write 
  input                       aux_irq_ren_r,     // Valid aux access
  input      [`npuarc_AUX_REG_RANGE] aux_irq_raddr_r,   // Aux read address
  input                       aux_irq_wen_r,     // Aux write operation
  input      [`npuarc_AUX_REG_RANGE] aux_irq_waddr_r,   // Aux write address
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input      [`npuarc_DATA_RANGE]    aux_wdata,         // Aux write data
  // leda NTL_CON13C on
  output reg [`npuarc_DATA_RANGE]    irq_aux_rdata,     // LR read data
  output reg                  irq_aux_illegal,   // SR/LR operation is illegal
  output reg                  irq_aux_k_rd,      // op needs Kernel R perm
  output reg                  irq_aux_k_wr,      // op needs Kernel W perm
  output reg                  irq_aux_unimpl,    // LR/SR reg is not present
  output reg                  irq_aux_serial_sr, // SR must serialize the pipe
  output reg                  irq_aux_strict_sr, // 

  /////////// Processor-side Interrupt Interface /////////////////////////////
  //
  input      [`npuarc_IRQN_RANGE]    cpu_accept_irq,// CPU-acceptable IRQ priorities
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Irq interface
  // leda NTL_CON13C on
  input      [`npuarc_IRQLGN_RANGE]  irq_ack_w_r,   // Ack. priority. Aligned with cpu_irq_select
  output reg                  irq_req,       // There is an enabled, active IRQ
  output reg [7:0]            irq_num,       // Prioritized IRQ number for irq_req
  output reg [`npuarc_IRQLGN_RANGE]  irq_w,         // Interrupt priority level for irq_req
  output reg                  irq_preempts,  // current irq_req preempts last irq
                                             // After irq_ack if irq_req stays on but
                                             // irq_preempts if off, it means a same level irq
  output                      irq_preempts_nxt, //irq_preempts before sync

  /////////// Processor-side Acknowledge Interface ///////////////////////////
  //
  input                       irq_ack,       // Interrupt acknowledge. current irq should be cleared
  input      [7:0]            irq_ack_num,   // Interrupt input ID (number) that is acknowledged

  /////////// ICAUSE register ////////////////////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]    ar_aux_icause0_r,
  output reg [`npuarc_DATA_RANGE]    ar_aux_icause1_r,
  output reg [`npuarc_DATA_RANGE]    ar_aux_icause2_r,
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input [`npuarc_DATA_RANGE] ar_aux_irq_act_r,      // Active interrupts, set by int_enter_evt, cleared by int_exit_event 
  // leda NTL_CON13C on
  ////////// Interrupt signals ///////////////////////////////////////////////
  //
  input      [`npuarc_IRQE_RANGE]    irq_r,         // synchronized external interrupt inputs
  ////////// Timer0 interrupt ////////////////////////////////////////////////
  //
  input [`npuarc_IRQM_RANGE]         timer0_irq_1h, // One-hot-encoded timer0 int

  ////////// Watchdog interrupt ////////////////////////////////////////////////
  //
  input [`npuarc_IRQM_RANGE]         wdt_int_timeout_1h_r, // One-hot-encoded watchdog int
  input  [`npuarc_IRQM_RANGE]         pct_int_overflow_r,
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  // leda NTL_CON13C on
  /////////// clk phase to enable irq output /////////////////////////////////
  // irq_clk_en_r is a 1 or 2 cycle clock enable signal that samples interrupt 
  // requests -- it includes input to irq (irq_r, timer0_irq_1h and timer1_irq_1h)
  //      as well as output from irq_unit (irq_req, irq_num, irq_w and irq_preempts)
  //
  input                      irq_clk_en_r,

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,
  input                       rst_a
  );

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Signal/Register Declerations                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// aux_PROC
//
reg                      aux_irq_hint_sel;
reg                      aux_irq_interrupt_sel;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not used in all configs
reg                      aux_priority_sel;
// leda NTL_CON13A on
reg                      aux_enable_sel;
reg                      aux_trigger_sel;
reg                      aux_irq_pulse_cancel_sel;
reg                      aux_irq_pulse_cancel_sel_r;
reg                      aux_wdata0_r;
reg                      aux_irq_ctl_sel; //to identify a aux register write that will affect irq output
reg [`npuarc_DATA_RANGE]        base_rdata;
reg                      base_unimpl;
reg [`npuarc_AUX_REG_RANGE]     qual_aux_addr;

// irq_ack_PROC
//
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
reg [`npuarc_IRQM_RANGE]        irq_ack_num_1h;
// leda NTL_CON13A on
reg irq_ack_r;
reg [7:0] irq_ack_num_r;

// edge_PROC
//
reg [`npuarc_IRQE_RANGE]        irq_edge_nxt;
reg [`npuarc_IRQE_RANGE]        irq_edge_en;
reg [`npuarc_IRQE_RANGE]        irq_edge_t01;
reg [`npuarc_IRQE_RANGE]        pending_nxt;
reg                      pending_update;
reg                      pending_clear_nxt;

// irq_outstanding_PROC
//
reg                      aux_irq_hint_en;
reg [`npuarc_IRQM_RANGE]        aux_irq_pending_nop;
reg [`npuarc_IRQM_RANGE]        aux_irq_pending;
reg [`npuarc_IRQM_RANGE]        aux_irq_hint_1h;

// irq_choose_PROC
//
reg [`npuarc_IRQM_RANGE]        irq_l_0;
reg [`npuarc_IRQM_RANGE]        irq_lbitmap_0;
reg [`npuarc_IRQM_RANGE]        irq_l_1;
reg [`npuarc_IRQM_RANGE]        irq_lbitmap_1;
reg [`npuarc_IRQM_RANGE]        irq_l_2;
reg [`npuarc_IRQM_RANGE]        irq_lbitmap_2;
reg [`npuarc_IRQM_RANGE]        irq_lsel;
reg [`npuarc_IRQLGN_RANGE]      irq_w_nxt;
reg [7:0]                irq_num_nxt;
reg                      irq_req_nxt;
reg [`npuarc_IRQN_RANGE]        irq_l_comb_r;
reg                      irq_preempts_pre;

// icause_PROC
//
reg [`npuarc_IRQN_RANGE]        irq_ack_w_1h;
reg [`npuarc_IRQLGM16_RANGE]    icause_nxt;
reg [`npuarc_IRQN_RANGE]        icause_wen;

// irq_interrupt_PROC
//
reg [`npuarc_DATA_RANGE]        aux_irq_pending_out;
reg [`npuarc_DATA_RANGE]        aux_irq_trigger_out;

reg [`npuarc_DATA_RANGE]        aux_irq_status_out;
reg [`npuarc_IRQE_RANGE]        aux_irq_trigger_en;
reg [`npuarc_IRQE_RANGE]        aux_irq_pulse_cancel;
reg [`npuarc_IRQM_RANGE]        aux_irq_interrupt_1h;
reg                      aux_irq_interrupt_en;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_nxt;
reg [`npuarc_DATA_RANGE]        aux_irq_priority_out;
reg [`npuarc_IRQM_RANGE]        aux_irq_priority_en;
reg [`npuarc_DATA_RANGE]        aux_irq_enable_out;
reg [`npuarc_IRQM_RANGE]        aux_irq_enable_en;

reg                      rdata_unimpl;

reg [`npuarc_IRQLGM16_RANGE]    aux_irq_hint_r;
reg [`npuarc_IRQLGM16_RANGE]    aux_irq_interrupt_r;
reg [`npuarc_IRQLGM16_RANGE]    aux_irq_interrupt_nxt;

// irq_level_reg_PROC
//
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_16_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_17_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_18_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_19_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_20_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_21_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_22_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_23_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_24_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_25_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_26_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_27_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_28_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_29_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_30_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_31_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_32_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_33_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_34_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_35_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_36_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_37_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_38_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_39_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_40_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_41_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_42_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_43_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_44_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_45_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_46_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_47_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_48_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_49_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_50_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_51_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_52_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_53_r;
reg [`npuarc_IRQLGN_RANGE]      aux_irq_priority_54_r;
reg [`npuarc_IRQM_RANGE]        aux_irq_enable_r;

reg [`npuarc_IRQE_RANGE]        aux_irq_trigger_r;

// icause_reg_PROC
//
reg [`npuarc_IRQLGM16_RANGE]    icause_0_r;
reg [`npuarc_IRQLGM16_RANGE]    icause_1_r;
reg [`npuarc_IRQLGM16_RANGE]    icause_2_r;

// pending_reg_PROC
//
reg [`npuarc_IRQE_RANGE]        pending_r;

reg                      pending_clear_r;

// edge_reg_PROC
//
reg [`npuarc_IRQE_RANGE]        irq_edge_r;
// out_reg_PROC
//
reg                      irq_req_r;      //flopped version of irq
reg [7:0]                irq_num_r;      //flopped version of irq_num
reg [`npuarc_IRQLGN_RANGE]      irq_w_r;        //flopped version of irq_w 
reg                      irq_preempts_r; //flopped version of irq_preempts
// update_ctl_PROC
//
reg                      aux_irq_update_kill;
reg                      irq_ack_update_kill;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @aux_PROC: Auxiliary register decode comb.                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: aux_read_PROC

  // AUX bus output.
  //
  irq_aux_illegal       = 1'b0;
  irq_aux_k_rd          = 1'b0;
  irq_aux_k_wr          = 1'b0;
  irq_aux_serial_sr     = 1'b0;
  irq_aux_strict_sr     = 1'b0;

  base_unimpl           = 1'b1;

  // Baseline register rdata
  //
  base_rdata        = `npuarc_DATA_SIZE'b0;

  // Qualify AUX addr,write,read lines by the commit/enable
  // signal to prevent unnecessary switching.
  //
  qual_aux_addr     = aux_irq_raddr_r & {`npuarc_AUX_REG_BITS{aux_irq_ren_r}};

  if (aux_irq_ren_r) begin
    base_unimpl            = 1'b0; 
    case (qual_aux_addr)

    `npuarc_IRQ_HINT_AUX: begin
      // Rep:CPU,P:RW,C:1:B:Ceil(log2(M))
      irq_aux_k_wr         = 1'b1;
      irq_aux_k_rd         = 1'b1;
      base_rdata[`npuarc_IRQLGM16_RANGE] = aux_irq_hint_r;
      irq_aux_serial_sr     = aux_write;
      irq_aux_strict_sr     = aux_write;
    end

    `npuarc_IRQ_LEVEL_PENDING_AUX: begin
      // Rep:SYSTEM,P:R,C:1,B:N
      irq_aux_k_rd          = 1'b1;
      irq_aux_illegal       = aux_write;
      // leda W563 off
      // LMD: Reduction of single bit expression is redundant
      // LJ: configurable field may be a single bit
      base_rdata[0]        = irq_l_comb_r[0];
      base_rdata[1]        = irq_l_comb_r[1];
      base_rdata[2]        = irq_l_comb_r[2];
      // leda W563 on
    end

    `npuarc_IRQ_INTERRUPT_AUX: begin
      // Rep:CPU,P:RW,C:C,B:Ceil(log2(M))
      irq_aux_k_wr           = 1'b1;
      irq_aux_k_rd           = 1'b1;
      base_rdata[`npuarc_IRQLGM16_RANGE] =
             aux_irq_interrupt_r[`npuarc_IRQLGM16_RANGE];

      irq_aux_serial_sr     = aux_write;
    end

    `npuarc_IRQ_PRIORITY_AUX: begin
      // Rep:IRQ,P:RW,C:M,B:N
      irq_aux_k_wr           = 1'b1;
      irq_aux_k_rd           = 1'b1;
      irq_aux_serial_sr     = aux_write;

    end

    `npuarc_IRQ_PENDING_AUX: begin
      // Rep:IRQ,P:R,C:M,B:1
      irq_aux_k_rd           = 1'b1;
      irq_aux_k_wr           = 1'b1;
      irq_aux_illegal        = aux_write;
    end

    `npuarc_IRQ_ENABLE_AUX: begin
      // Rep:IRQ,P:RW,C:M,B:1
      irq_aux_k_wr           = 1'b1;
      irq_aux_k_rd           = 1'b1;
      irq_aux_serial_sr     = aux_write;

    end

    `npuarc_IRQ_TRIGGER_AUX: begin
      // Rep:IRQ,P:RW,C:M,B:1
      irq_aux_k_wr           = 1'b1;
      irq_aux_k_rd           = 1'b1;
      irq_aux_serial_sr     = aux_write;

    end

    `npuarc_IRQ_PULSE_CANCEL_AUX: begin
      // Rep:IRQ,P:W,C:M,B:1
      irq_aux_k_wr           = 1'b1;
      irq_aux_k_rd           = 1'b1;
      irq_aux_illegal        = aux_read;

    end

    `npuarc_IRQ_STATUS_AUX: begin
      // Rep:IRQ,P:R,C:M,B:N+3
      irq_aux_k_wr           = 1'b1;
      irq_aux_k_rd           = 1'b1;
      irq_aux_illegal        = aux_write;
    end

    `npuarc_ICAUSE_AUX: begin
       // leda W226 off
      // LMD: case select expression is constant
      // LJ:  "case (1'b1)" is used for a one-hot decoder
       // leda W225 off
      // LMD: case item expression is not constant
      // LJ:  requirement of one-hot decoder case statement
       case (1'b1)
         ar_aux_irq_act_r[0]:
           base_rdata        = ar_aux_icause0_r;
         ar_aux_irq_act_r[1]:
           base_rdata        = ar_aux_icause1_r;
         ar_aux_irq_act_r[2]:
           base_rdata        = ar_aux_icause2_r;
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
       default: ;
       endcase
       // leda W226 on
       // leda W225 on
// spyglass enable_block W193
       irq_aux_k_rd     = 1'b1;
       irq_aux_illegal  = aux_write;
    end

    default: begin
      base_unimpl        = 1'b1;
    end
    endcase // case (qual_aux_addr)
  end

end // block: aux_PROC

always @*
begin: aux_write_PROC

  // Register selects.
  //
  aux_irq_hint_sel         = 1'b0;
  aux_irq_interrupt_sel    = 1'b0;
  aux_priority_sel         = 1'b0;
  aux_enable_sel           = 1'b0;
  aux_trigger_sel          = 1'b0;
  aux_irq_ctl_sel          = aux_irq_wen_r;
  aux_irq_pulse_cancel_sel = 1'b0;

  if (aux_irq_wen_r) begin
    case (aux_irq_waddr_r)
    `npuarc_IRQ_HINT_AUX: begin
      aux_irq_hint_sel   = 1'b1;
    end
    `npuarc_IRQ_INTERRUPT_AUX: begin
      aux_irq_interrupt_sel  = 1'b1;
      aux_irq_ctl_sel        = 1'b0;
    end
    `npuarc_IRQ_PRIORITY_AUX: begin
      aux_priority_sel   = 1'b1;
    end
    `npuarc_IRQ_ENABLE_AUX: begin
      aux_enable_sel     = 1'b1;
    end
    `npuarc_IRQ_TRIGGER_AUX: begin
      aux_trigger_sel    = 1'b1;
    end
    `npuarc_IRQ_PULSE_CANCEL_AUX: begin
      aux_irq_pulse_cancel_sel = 1'b1;
    end
    default: begin
      aux_irq_hint_sel    = 1'b0;
      aux_irq_ctl_sel     = 1'b0;
    end
    endcase
  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_ack_PROC: Interrupt acknowledgement                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_ack_PROC

  // Derive a 1-hot vector to denote the current interrupt being
  // acknowledged (normalised for the + 16 offset).
  //
  // leda W71 off
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  irq_ack_num_1h    = `npuarc_IRQ_M'b0;
  case (irq_ack_num_r)
    8'd16:
      irq_ack_num_1h[16]   = 1'b1;
    8'd17:
      irq_ack_num_1h[17]   = 1'b1;
    8'd18:
      irq_ack_num_1h[18]   = 1'b1;
    8'd19:
      irq_ack_num_1h[19]   = 1'b1;
    8'd20:
      irq_ack_num_1h[20]   = 1'b1;
    8'd21:
      irq_ack_num_1h[21]   = 1'b1;
    8'd22:
      irq_ack_num_1h[22]   = 1'b1;
    8'd23:
      irq_ack_num_1h[23]   = 1'b1;
    8'd24:
      irq_ack_num_1h[24]   = 1'b1;
    8'd25:
      irq_ack_num_1h[25]   = 1'b1;
    8'd26:
      irq_ack_num_1h[26]   = 1'b1;
    8'd27:
      irq_ack_num_1h[27]   = 1'b1;
    8'd28:
      irq_ack_num_1h[28]   = 1'b1;
    8'd29:
      irq_ack_num_1h[29]   = 1'b1;
    8'd30:
      irq_ack_num_1h[30]   = 1'b1;
    8'd31:
      irq_ack_num_1h[31]   = 1'b1;
    8'd32:
      irq_ack_num_1h[32]   = 1'b1;
    8'd33:
      irq_ack_num_1h[33]   = 1'b1;
    8'd34:
      irq_ack_num_1h[34]   = 1'b1;
    8'd35:
      irq_ack_num_1h[35]   = 1'b1;
    8'd36:
      irq_ack_num_1h[36]   = 1'b1;
    8'd37:
      irq_ack_num_1h[37]   = 1'b1;
    8'd38:
      irq_ack_num_1h[38]   = 1'b1;
    8'd39:
      irq_ack_num_1h[39]   = 1'b1;
    8'd40:
      irq_ack_num_1h[40]   = 1'b1;
    8'd41:
      irq_ack_num_1h[41]   = 1'b1;
    8'd42:
      irq_ack_num_1h[42]   = 1'b1;
    8'd43:
      irq_ack_num_1h[43]   = 1'b1;
    8'd44:
      irq_ack_num_1h[44]   = 1'b1;
    8'd45:
      irq_ack_num_1h[45]   = 1'b1;
    8'd46:
      irq_ack_num_1h[46]   = 1'b1;
    8'd47:
      irq_ack_num_1h[47]   = 1'b1;
    8'd48:
      irq_ack_num_1h[48]   = 1'b1;
    8'd49:
      irq_ack_num_1h[49]   = 1'b1;
    8'd50:
      irq_ack_num_1h[50]   = 1'b1;
    8'd51:
      irq_ack_num_1h[51]   = 1'b1;
    8'd52:
      irq_ack_num_1h[52]   = 1'b1;
    8'd53:
      irq_ack_num_1h[53]   = 1'b1;
    8'd54:
      irq_ack_num_1h[54]   = 1'b1;
  endcase
  // leda DFT_022 on
  // leda W71 on

end // block: irq_ack_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @edge_PROC: Edge/Pulse interrupt comb.                                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: edge_PROC

  irq_edge_nxt      = irq_r;

  // As a power saving measure, enable only those 'Edge' registers
  // that correspond to interrupt lines that are configured to be edge
  // sensitive. Given that these interrupts will likely respresent
  // only a small subset of all interrupts, we can potentially prevent
  // a lot of unnecessary switching.
  //
  irq_edge_en[16]   = aux_irq_trigger_r[16];
  irq_edge_en[17]   = aux_irq_trigger_r[17];
  irq_edge_en[18]   = aux_irq_trigger_r[18];
  irq_edge_en[19]   = aux_irq_trigger_r[19];
  irq_edge_en[20]   = aux_irq_trigger_r[20];
  irq_edge_en[21]   = aux_irq_trigger_r[21];
  irq_edge_en[22]   = aux_irq_trigger_r[22];
  irq_edge_en[23]   = aux_irq_trigger_r[23];
  irq_edge_en[24]   = aux_irq_trigger_r[24];
  irq_edge_en[25]   = aux_irq_trigger_r[25];
  irq_edge_en[26]   = aux_irq_trigger_r[26];
  irq_edge_en[27]   = aux_irq_trigger_r[27];
  irq_edge_en[28]   = aux_irq_trigger_r[28];
  irq_edge_en[29]   = aux_irq_trigger_r[29];
  irq_edge_en[30]   = aux_irq_trigger_r[30];
  irq_edge_en[31]   = aux_irq_trigger_r[31];
  irq_edge_en[32]   = aux_irq_trigger_r[32];
  irq_edge_en[33]   = aux_irq_trigger_r[33];
  irq_edge_en[34]   = aux_irq_trigger_r[34];
  irq_edge_en[35]   = aux_irq_trigger_r[35];
  irq_edge_en[36]   = aux_irq_trigger_r[36];
  irq_edge_en[37]   = aux_irq_trigger_r[37];
  irq_edge_en[38]   = aux_irq_trigger_r[38];
  irq_edge_en[39]   = aux_irq_trigger_r[39];
  irq_edge_en[40]   = aux_irq_trigger_r[40];
  irq_edge_en[41]   = aux_irq_trigger_r[41];
  irq_edge_en[42]   = aux_irq_trigger_r[42];
  irq_edge_en[43]   = aux_irq_trigger_r[43];
  irq_edge_en[44]   = aux_irq_trigger_r[44];
  irq_edge_en[45]   = aux_irq_trigger_r[45];
  irq_edge_en[46]   = aux_irq_trigger_r[46];
  irq_edge_en[47]   = aux_irq_trigger_r[47];
  irq_edge_en[48]   = aux_irq_trigger_r[48];
  irq_edge_en[49]   = aux_irq_trigger_r[49];
  irq_edge_en[50]   = aux_irq_trigger_r[50];
  irq_edge_en[51]   = aux_irq_trigger_r[51];
  irq_edge_en[52]   = aux_irq_trigger_r[52];
  irq_edge_en[53]   = aux_irq_trigger_r[53];
  irq_edge_en[54]   = aux_irq_trigger_r[54];

  // Transition ('t') 0 -> 1
  //
  irq_edge_t01      = ~irq_edge_r & irq_edge_nxt;

  // The vector denoting the edge trigger pending interrupts is
  // defined by the subset of the incoming interrupts that are set
  // to be edge triggered OR, the existing set of pending
  // interrupts, with the bit of the currently acknowledged
  // interrupt cleared.
  //
// leda W563 off 
      // LMD: Reduction of single bit expression is redundant
      // LJ: configurable field may be a single bit
  pending_nxt       = ~aux_irq_pulse_cancel
                    & (   (   (irq_edge_t01 & aux_irq_trigger_r)
                            |  pending_r
                          )
                        & (   (   irq_ack_num_1h[`npuarc_IRQE_RANGE]
                                ^ {`npuarc_IRQ_E{irq_ack_r}}
                               )
                            | {`npuarc_IRQ_E{~irq_ack_r}}
                          )
                      )
                    ;
  pending_update    = (|aux_irq_pulse_cancel) 
                    | irq_ack_r
                    | irq_clk_en_r
                    ; 


  // Clear the interrupt request line for the IRQ_OUTPUT_REG case when
  // the final outstanding interrupt is edge-triggered. In this case,
  // the interrupt request has to be deasserted on the cycle cycle
  // after the assertion of the interrupt acknowledgement. In the
  // absence of this logic, and because of the additional output
  // register, this operation would typically be delayed by one cycle
  // causing the interrupt to be taken twice. This logic only applies
  // to edge-triggered interrupts given that only these have any
  // dependency upon irq_ack.
  //
// spyglass disable_block Ac_conv01
// SMD: cdc sync signals converging on combinational gate
// SJ:  cdc syncs are independent and chance of glitch is very low
  pending_clear_nxt = (|(pending_r & (~pending_nxt)))
                    & (~(|aux_irq_pending_nop))
                    ;
// spyglass enable_block Ac_conv01
// leda W563 on 

end // block: edge_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_outstanding_PROC: Interrupt consolidation comb.                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_outstanding_PROC

  // HINT register. Decode hint accesses and convert to one-hot
  // vector.
  //
  // leda W71 off
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  aux_irq_hint_1h   = `npuarc_IRQ_M'b0;
  case (aux_irq_hint_r)
    `npuarc_IRQLGM16_BITS'd16: aux_irq_hint_1h[16] = 1'b1;
    `npuarc_IRQLGM16_BITS'd17: aux_irq_hint_1h[17] = 1'b1;
    `npuarc_IRQLGM16_BITS'd18: aux_irq_hint_1h[18] = 1'b1;
    `npuarc_IRQLGM16_BITS'd19: aux_irq_hint_1h[19] = 1'b1;
    `npuarc_IRQLGM16_BITS'd20: aux_irq_hint_1h[20] = 1'b1;
    `npuarc_IRQLGM16_BITS'd21: aux_irq_hint_1h[21] = 1'b1;
    `npuarc_IRQLGM16_BITS'd22: aux_irq_hint_1h[22] = 1'b1;
    `npuarc_IRQLGM16_BITS'd23: aux_irq_hint_1h[23] = 1'b1;
    `npuarc_IRQLGM16_BITS'd24: aux_irq_hint_1h[24] = 1'b1;
    `npuarc_IRQLGM16_BITS'd25: aux_irq_hint_1h[25] = 1'b1;
    `npuarc_IRQLGM16_BITS'd26: aux_irq_hint_1h[26] = 1'b1;
    `npuarc_IRQLGM16_BITS'd27: aux_irq_hint_1h[27] = 1'b1;
    `npuarc_IRQLGM16_BITS'd28: aux_irq_hint_1h[28] = 1'b1;
    `npuarc_IRQLGM16_BITS'd29: aux_irq_hint_1h[29] = 1'b1;
    `npuarc_IRQLGM16_BITS'd30: aux_irq_hint_1h[30] = 1'b1;
    `npuarc_IRQLGM16_BITS'd31: aux_irq_hint_1h[31] = 1'b1;
    `npuarc_IRQLGM16_BITS'd32: aux_irq_hint_1h[32] = 1'b1;
    `npuarc_IRQLGM16_BITS'd33: aux_irq_hint_1h[33] = 1'b1;
    `npuarc_IRQLGM16_BITS'd34: aux_irq_hint_1h[34] = 1'b1;
    `npuarc_IRQLGM16_BITS'd35: aux_irq_hint_1h[35] = 1'b1;
    `npuarc_IRQLGM16_BITS'd36: aux_irq_hint_1h[36] = 1'b1;
    `npuarc_IRQLGM16_BITS'd37: aux_irq_hint_1h[37] = 1'b1;
    `npuarc_IRQLGM16_BITS'd38: aux_irq_hint_1h[38] = 1'b1;
    `npuarc_IRQLGM16_BITS'd39: aux_irq_hint_1h[39] = 1'b1;
    `npuarc_IRQLGM16_BITS'd40: aux_irq_hint_1h[40] = 1'b1;
    `npuarc_IRQLGM16_BITS'd41: aux_irq_hint_1h[41] = 1'b1;
    `npuarc_IRQLGM16_BITS'd42: aux_irq_hint_1h[42] = 1'b1;
    `npuarc_IRQLGM16_BITS'd43: aux_irq_hint_1h[43] = 1'b1;
    `npuarc_IRQLGM16_BITS'd44: aux_irq_hint_1h[44] = 1'b1;
    `npuarc_IRQLGM16_BITS'd45: aux_irq_hint_1h[45] = 1'b1;
    `npuarc_IRQLGM16_BITS'd46: aux_irq_hint_1h[46] = 1'b1;
    `npuarc_IRQLGM16_BITS'd47: aux_irq_hint_1h[47] = 1'b1;
    `npuarc_IRQLGM16_BITS'd48: aux_irq_hint_1h[48] = 1'b1;
    `npuarc_IRQLGM16_BITS'd49: aux_irq_hint_1h[49] = 1'b1;
    `npuarc_IRQLGM16_BITS'd50: aux_irq_hint_1h[50] = 1'b1;
    `npuarc_IRQLGM16_BITS'd51: aux_irq_hint_1h[51] = 1'b1;
    `npuarc_IRQLGM16_BITS'd52: aux_irq_hint_1h[52] = 1'b1;
    `npuarc_IRQLGM16_BITS'd53: aux_irq_hint_1h[53] = 1'b1;
    `npuarc_IRQLGM16_BITS'd54: aux_irq_hint_1h[54] = 1'b1;
  endcase // case (aux_irq_hint_r)
  // leda DFT_022 on
  // leda W71 on
  aux_irq_hint_en   = aux_irq_hint_sel;

  // Derive an IRQ_M-bit vector containing the list of currently
  // asserted interrupts at any level. This is derived by -simply-
  // calculating the or-reduction of all possible interrupt
  // sources. Interrupt sources, (1) resynchronised input, (2)
  // outstanding edge-sensitive, (3) timer 0 interrupt pending, (4)
  // timer 1 interrupt pending, (5) hint register for all attached
  // CPU.
  //
  aux_irq_pending_nop  = aux_irq_hint_1h              // (5)
                       |( {
                              irq_r
                            & (~aux_irq_trigger_r)    // (1)
                          }
                        )
                       | timer0_irq_1h                // (3)
                       | wdt_int_timeout_1h_r                // (5)
                       | pct_int_overflow_r
                       ;

  // The vector containing the outstanding interrupts and additionally
  // any outstanding edge-triggered interrupts.
  //
  aux_irq_pending      = aux_irq_pending_nop
                       | {
                           pending_r                  // (2)
                         }
                       ;

end // block: irq_outstanding_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_lbitmap0_PROC: Interrupt allocation bitmap                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_lbitmap0_PROC

  // Interrupt allocation bitmap [0,39]:
  //
  // Compile a IRQ_N, IRQ_M-bit bit-vectors where the presence of a
  // one represents the presence of an interrupt allocated to the
  // current level.
  //

  irq_lbitmap_0[16]    = aux_irq_enable_r[16]
                         & (aux_irq_priority_16_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[17]    = aux_irq_enable_r[17]
                         & (aux_irq_priority_17_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[18]    = aux_irq_enable_r[18]
                         & (aux_irq_priority_18_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[19]    = aux_irq_enable_r[19]
                         & (aux_irq_priority_19_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[20]    = aux_irq_enable_r[20]
                         & (aux_irq_priority_20_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[21]    = aux_irq_enable_r[21]
                         & (aux_irq_priority_21_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[22]    = aux_irq_enable_r[22]
                         & (aux_irq_priority_22_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[23]    = aux_irq_enable_r[23]
                         & (aux_irq_priority_23_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[24]    = aux_irq_enable_r[24]
                         & (aux_irq_priority_24_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[25]    = aux_irq_enable_r[25]
                         & (aux_irq_priority_25_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[26]    = aux_irq_enable_r[26]
                         & (aux_irq_priority_26_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[27]    = aux_irq_enable_r[27]
                         & (aux_irq_priority_27_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[28]    = aux_irq_enable_r[28]
                         & (aux_irq_priority_28_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[29]    = aux_irq_enable_r[29]
                         & (aux_irq_priority_29_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[30]    = aux_irq_enable_r[30]
                         & (aux_irq_priority_30_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[31]    = aux_irq_enable_r[31]
                         & (aux_irq_priority_31_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[32]    = aux_irq_enable_r[32]
                         & (aux_irq_priority_32_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[33]    = aux_irq_enable_r[33]
                         & (aux_irq_priority_33_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[34]    = aux_irq_enable_r[34]
                         & (aux_irq_priority_34_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[35]    = aux_irq_enable_r[35]
                         & (aux_irq_priority_35_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[36]    = aux_irq_enable_r[36]
                         & (aux_irq_priority_36_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[37]    = aux_irq_enable_r[37]
                         & (aux_irq_priority_37_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[38]    = aux_irq_enable_r[38]
                         & (aux_irq_priority_38_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[39]    = aux_irq_enable_r[39]
                         & (aux_irq_priority_39_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[40]    = aux_irq_enable_r[40]
                         & (aux_irq_priority_40_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[41]    = aux_irq_enable_r[41]
                         & (aux_irq_priority_41_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[42]    = aux_irq_enable_r[42]
                         & (aux_irq_priority_42_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[43]    = aux_irq_enable_r[43]
                         & (aux_irq_priority_43_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[44]    = aux_irq_enable_r[44]
                         & (aux_irq_priority_44_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[45]    = aux_irq_enable_r[45]
                         & (aux_irq_priority_45_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[46]    = aux_irq_enable_r[46]
                         & (aux_irq_priority_46_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[47]    = aux_irq_enable_r[47]
                         & (aux_irq_priority_47_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[48]    = aux_irq_enable_r[48]
                         & (aux_irq_priority_48_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[49]    = aux_irq_enable_r[49]
                         & (aux_irq_priority_49_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[50]    = aux_irq_enable_r[50]
                         & (aux_irq_priority_50_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[51]    = aux_irq_enable_r[51]
                         & (aux_irq_priority_51_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[52]    = aux_irq_enable_r[52]
                         & (aux_irq_priority_52_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[53]    = aux_irq_enable_r[53]
                         & (aux_irq_priority_53_r == `npuarc_IRQLGN_BITS'd0)
                         ;

  irq_lbitmap_0[54]    = aux_irq_enable_r[54]
                         & (aux_irq_priority_54_r == `npuarc_IRQLGN_BITS'd0)
                         ;

end // block: irq_lbitmap0


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_lbitmap1_PROC: Interrupt allocation bitmap                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_lbitmap1_PROC

  // Interrupt allocation bitmap [1,39]:
  //
  // Compile a IRQ_N, IRQ_M-bit bit-vectors where the presence of a
  // one represents the presence of an interrupt allocated to the
  // current level.
  //

  irq_lbitmap_1[16]    = aux_irq_enable_r[16]
                         & (aux_irq_priority_16_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[17]    = aux_irq_enable_r[17]
                         & (aux_irq_priority_17_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[18]    = aux_irq_enable_r[18]
                         & (aux_irq_priority_18_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[19]    = aux_irq_enable_r[19]
                         & (aux_irq_priority_19_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[20]    = aux_irq_enable_r[20]
                         & (aux_irq_priority_20_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[21]    = aux_irq_enable_r[21]
                         & (aux_irq_priority_21_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[22]    = aux_irq_enable_r[22]
                         & (aux_irq_priority_22_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[23]    = aux_irq_enable_r[23]
                         & (aux_irq_priority_23_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[24]    = aux_irq_enable_r[24]
                         & (aux_irq_priority_24_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[25]    = aux_irq_enable_r[25]
                         & (aux_irq_priority_25_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[26]    = aux_irq_enable_r[26]
                         & (aux_irq_priority_26_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[27]    = aux_irq_enable_r[27]
                         & (aux_irq_priority_27_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[28]    = aux_irq_enable_r[28]
                         & (aux_irq_priority_28_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[29]    = aux_irq_enable_r[29]
                         & (aux_irq_priority_29_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[30]    = aux_irq_enable_r[30]
                         & (aux_irq_priority_30_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[31]    = aux_irq_enable_r[31]
                         & (aux_irq_priority_31_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[32]    = aux_irq_enable_r[32]
                         & (aux_irq_priority_32_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[33]    = aux_irq_enable_r[33]
                         & (aux_irq_priority_33_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[34]    = aux_irq_enable_r[34]
                         & (aux_irq_priority_34_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[35]    = aux_irq_enable_r[35]
                         & (aux_irq_priority_35_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[36]    = aux_irq_enable_r[36]
                         & (aux_irq_priority_36_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[37]    = aux_irq_enable_r[37]
                         & (aux_irq_priority_37_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[38]    = aux_irq_enable_r[38]
                         & (aux_irq_priority_38_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[39]    = aux_irq_enable_r[39]
                         & (aux_irq_priority_39_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[40]    = aux_irq_enable_r[40]
                         & (aux_irq_priority_40_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[41]    = aux_irq_enable_r[41]
                         & (aux_irq_priority_41_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[42]    = aux_irq_enable_r[42]
                         & (aux_irq_priority_42_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[43]    = aux_irq_enable_r[43]
                         & (aux_irq_priority_43_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[44]    = aux_irq_enable_r[44]
                         & (aux_irq_priority_44_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[45]    = aux_irq_enable_r[45]
                         & (aux_irq_priority_45_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[46]    = aux_irq_enable_r[46]
                         & (aux_irq_priority_46_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[47]    = aux_irq_enable_r[47]
                         & (aux_irq_priority_47_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[48]    = aux_irq_enable_r[48]
                         & (aux_irq_priority_48_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[49]    = aux_irq_enable_r[49]
                         & (aux_irq_priority_49_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[50]    = aux_irq_enable_r[50]
                         & (aux_irq_priority_50_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[51]    = aux_irq_enable_r[51]
                         & (aux_irq_priority_51_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[52]    = aux_irq_enable_r[52]
                         & (aux_irq_priority_52_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[53]    = aux_irq_enable_r[53]
                         & (aux_irq_priority_53_r == `npuarc_IRQLGN_BITS'd1)
                         ;

  irq_lbitmap_1[54]    = aux_irq_enable_r[54]
                         & (aux_irq_priority_54_r == `npuarc_IRQLGN_BITS'd1)
                         ;

end // block: irq_lbitmap1


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_lbitmap2_PROC: Interrupt allocation bitmap                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_lbitmap2_PROC

  // Interrupt allocation bitmap [2,39]:
  //
  // Compile a IRQ_N, IRQ_M-bit bit-vectors where the presence of a
  // one represents the presence of an interrupt allocated to the
  // current level.
  //

  irq_lbitmap_2[16]    = aux_irq_enable_r[16]
                         & (aux_irq_priority_16_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[17]    = aux_irq_enable_r[17]
                         & (aux_irq_priority_17_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[18]    = aux_irq_enable_r[18]
                         & (aux_irq_priority_18_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[19]    = aux_irq_enable_r[19]
                         & (aux_irq_priority_19_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[20]    = aux_irq_enable_r[20]
                         & (aux_irq_priority_20_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[21]    = aux_irq_enable_r[21]
                         & (aux_irq_priority_21_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[22]    = aux_irq_enable_r[22]
                         & (aux_irq_priority_22_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[23]    = aux_irq_enable_r[23]
                         & (aux_irq_priority_23_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[24]    = aux_irq_enable_r[24]
                         & (aux_irq_priority_24_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[25]    = aux_irq_enable_r[25]
                         & (aux_irq_priority_25_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[26]    = aux_irq_enable_r[26]
                         & (aux_irq_priority_26_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[27]    = aux_irq_enable_r[27]
                         & (aux_irq_priority_27_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[28]    = aux_irq_enable_r[28]
                         & (aux_irq_priority_28_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[29]    = aux_irq_enable_r[29]
                         & (aux_irq_priority_29_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[30]    = aux_irq_enable_r[30]
                         & (aux_irq_priority_30_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[31]    = aux_irq_enable_r[31]
                         & (aux_irq_priority_31_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[32]    = aux_irq_enable_r[32]
                         & (aux_irq_priority_32_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[33]    = aux_irq_enable_r[33]
                         & (aux_irq_priority_33_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[34]    = aux_irq_enable_r[34]
                         & (aux_irq_priority_34_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[35]    = aux_irq_enable_r[35]
                         & (aux_irq_priority_35_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[36]    = aux_irq_enable_r[36]
                         & (aux_irq_priority_36_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[37]    = aux_irq_enable_r[37]
                         & (aux_irq_priority_37_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[38]    = aux_irq_enable_r[38]
                         & (aux_irq_priority_38_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[39]    = aux_irq_enable_r[39]
                         & (aux_irq_priority_39_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[40]    = aux_irq_enable_r[40]
                         & (aux_irq_priority_40_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[41]    = aux_irq_enable_r[41]
                         & (aux_irq_priority_41_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[42]    = aux_irq_enable_r[42]
                         & (aux_irq_priority_42_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[43]    = aux_irq_enable_r[43]
                         & (aux_irq_priority_43_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[44]    = aux_irq_enable_r[44]
                         & (aux_irq_priority_44_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[45]    = aux_irq_enable_r[45]
                         & (aux_irq_priority_45_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[46]    = aux_irq_enable_r[46]
                         & (aux_irq_priority_46_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[47]    = aux_irq_enable_r[47]
                         & (aux_irq_priority_47_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[48]    = aux_irq_enable_r[48]
                         & (aux_irq_priority_48_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[49]    = aux_irq_enable_r[49]
                         & (aux_irq_priority_49_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[50]    = aux_irq_enable_r[50]
                         & (aux_irq_priority_50_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[51]    = aux_irq_enable_r[51]
                         & (aux_irq_priority_51_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[52]    = aux_irq_enable_r[52]
                         & (aux_irq_priority_52_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[53]    = aux_irq_enable_r[53]
                         & (aux_irq_priority_53_r == `npuarc_IRQLGN_BITS'd2)
                         ;

  irq_lbitmap_2[54]    = aux_irq_enable_r[54]
                         & (aux_irq_priority_54_r == `npuarc_IRQLGN_BITS'd2)
                         ;

end // block: irq_lbitmap2


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_choose_PROC: Interrupt decode comb.                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// For each interrupt line 'aux_irq_pending[i]', there is a unique
// priority level 'aux_irq_priority_39_r'. Priority resolutions occurs
// across two-dimensions: 1) firstly, the vertical priority number [0,
// IRQ_N), and 2) secondly, the interrupt number over the interval [0,
// IRQ_M). The following logic creates IRQ_N, IRQ_M bit-vectors
// denoting the priority level allocation for each interrupt
// configured, and selects lowest (highest priority) level for which
// there are outstanding interrupts. Once the interrupt level is
// determined, the IRQ_M bit-vector is priority encoded to select the
// highest priority interrupt within the group.
//

always @*
begin: irq_choose_PROC

  // Mask the outstanding vector with the level allocation and split
  // into seperate vectors, one for each level.
  //
  irq_l_0         = (   aux_irq_enable_r
                        & aux_irq_pending
                        & irq_lbitmap_0
                      )
                    ;
  irq_l_1         = (   aux_irq_enable_r
                        & aux_irq_pending
                        & irq_lbitmap_1
                      )
                    ;
  irq_l_2         = (   aux_irq_enable_r
                        & aux_irq_pending
                        & irq_lbitmap_2
                      )
                    ;

  // Select the highest level priority over the interval [0:`IRQ_N).
  // For the selected priority level, determine the following outputs:
  //
  //  (1) select the vector containing all of the outstanding
  //      interrupts at that level, to irq_lsel.
  //
  //  (2) assign the next 'W' priority level at which it occurs, to irq_w_nxt
  //
  //  (3) if the highest priority active interrupt is considered by
  //      the cpu to be high enough to preempt the cpu, and interrupts
  //      are enabled, then set irq_preempts to 1, otherwise set it to 0.
  //
  // leda W71 off
  // LMD: case block missing a default
  // LJ:  default term is covered prior to the case block
  // leda W225 off
      // LMD: case item expression is not constant
      // LJ:  requirement of one-hot decoder case statement
  // leda W226 off
      // LMD: case select expression is constant
      // LJ:  "case (1'b1)" is used for a one-hot decoder
  // leda W563 off
      // LMD: Reduction of single bit expression is redundant
      // LJ: configurable field may be a single bit
  // spyglass disable_block Ac_conv02
  // SMD: synchronizers converging on combinational gate
  // SJ:  false violation, aggregate set/clear only multicycle path
  irq_lsel          = `npuarc_IRQ_M'b0;
  irq_w_nxt         = `npuarc_IRQLGN_BITS'd0;
  irq_preempts_pre  = 1'b0;
  case (1'b1)
    (|irq_l_0): begin
      irq_lsel      = irq_l_0;                // (1)
      irq_w_nxt     = `npuarc_IRQLGN_BITS'd0;         // (2)
      irq_preempts_pre  = 1'b1 //timing isolation, cpu_accept_irq[0];  // (3)
                        ;
    end
    (|irq_l_1): begin
      irq_lsel      = irq_l_1;                // (1)
      irq_w_nxt     = `npuarc_IRQLGN_BITS'd1;         // (2)
      irq_preempts_pre  = 1'b1 //timing isolation, cpu_accept_irq[1];  // (3)
                        ;
    end
    (|irq_l_2): begin
      irq_lsel      = irq_l_2;                // (1)
      irq_w_nxt     = `npuarc_IRQLGN_BITS'd2;         // (2)
      irq_preempts_pre  = 1'b1 //timing isolation, cpu_accept_irq[2];  // (3)
                        ;
    end
  endcase
  // leda W71 on
  // leda W225 on
  // leda W226 on
  // leda W563 on
  // spyglass enable_block Ac_conv02

  // leda W226 off
      // LMD: case select expression is constant
      // LJ:  "case (1'b1)" is used for a one-hot decoder
  // leda W225 off
      // LMD: case item expression is not constant
      // LJ:  requirement of one-hot decoder case statement
  // leda W71 off
  // LMD: case block missing a default
  // LJ:  default term is covered prior to the case block
  irq_num_nxt       = 8'd0;
  case (1'b1)
    irq_lsel[16]: begin
      irq_num_nxt     = 8'd16;
    end
    irq_lsel[17]: begin
      irq_num_nxt     = 8'd17;
    end
    irq_lsel[18]: begin
      irq_num_nxt     = 8'd18;
    end
    irq_lsel[19]: begin
      irq_num_nxt     = 8'd19;
    end
    irq_lsel[20]: begin
      irq_num_nxt     = 8'd20;
    end
    irq_lsel[21]: begin
      irq_num_nxt     = 8'd21;
    end
    irq_lsel[22]: begin
      irq_num_nxt     = 8'd22;
    end
    irq_lsel[23]: begin
      irq_num_nxt     = 8'd23;
    end
    irq_lsel[24]: begin
      irq_num_nxt     = 8'd24;
    end
    irq_lsel[25]: begin
      irq_num_nxt     = 8'd25;
    end
    irq_lsel[26]: begin
      irq_num_nxt     = 8'd26;
    end
    irq_lsel[27]: begin
      irq_num_nxt     = 8'd27;
    end
    irq_lsel[28]: begin
      irq_num_nxt     = 8'd28;
    end
    irq_lsel[29]: begin
      irq_num_nxt     = 8'd29;
    end
    irq_lsel[30]: begin
      irq_num_nxt     = 8'd30;
    end
    irq_lsel[31]: begin
      irq_num_nxt     = 8'd31;
    end
    irq_lsel[32]: begin
      irq_num_nxt     = 8'd32;
    end
    irq_lsel[33]: begin
      irq_num_nxt     = 8'd33;
    end
    irq_lsel[34]: begin
      irq_num_nxt     = 8'd34;
    end
    irq_lsel[35]: begin
      irq_num_nxt     = 8'd35;
    end
    irq_lsel[36]: begin
      irq_num_nxt     = 8'd36;
    end
    irq_lsel[37]: begin
      irq_num_nxt     = 8'd37;
    end
    irq_lsel[38]: begin
      irq_num_nxt     = 8'd38;
    end
    irq_lsel[39]: begin
      irq_num_nxt     = 8'd39;
    end
    irq_lsel[40]: begin
      irq_num_nxt     = 8'd40;
    end
    irq_lsel[41]: begin
      irq_num_nxt     = 8'd41;
    end
    irq_lsel[42]: begin
      irq_num_nxt     = 8'd42;
    end
    irq_lsel[43]: begin
      irq_num_nxt     = 8'd43;
    end
    irq_lsel[44]: begin
      irq_num_nxt     = 8'd44;
    end
    irq_lsel[45]: begin
      irq_num_nxt     = 8'd45;
    end
    irq_lsel[46]: begin
      irq_num_nxt     = 8'd46;
    end
    irq_lsel[47]: begin
      irq_num_nxt     = 8'd47;
    end
    irq_lsel[48]: begin
      irq_num_nxt     = 8'd48;
    end
    irq_lsel[49]: begin
      irq_num_nxt     = 8'd49;
    end
    irq_lsel[50]: begin
      irq_num_nxt     = 8'd50;
    end
    irq_lsel[51]: begin
      irq_num_nxt     = 8'd51;
    end
    irq_lsel[52]: begin
      irq_num_nxt     = 8'd52;
    end
    irq_lsel[53]: begin
      irq_num_nxt     = 8'd53;
    end
    irq_lsel[54]: begin
      irq_num_nxt     = 8'd54;
    end
  endcase
  // leda W71 on
  // leda W225 on
  // leda W226 on

  // Assert irq_req_nxt if any pending interrupt is locally enabled.
  //
  irq_req_nxt       = (|(   aux_irq_pending
                         & aux_irq_enable_r
                       ))
                    ;
end // block: irq_choose_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @out_PROC: Output selection logic for large IRQ_N                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: out_PROC

  irq_req           = 1'b0
                    | (   irq_req_r
                        & (~pending_clear_r)
                      )
                    ;

  irq_num           = 8'd0
                    | irq_num_r
                    ;

  irq_w             = `npuarc_IRQLGN_BITS'd0
                    | irq_w_r
                    ;

  irq_preempts      = 1'b0
                    | irq_preempts_r
                    ;
end // block: out_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @icause_PROC: ICAUSE update logic                                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: icause_PROC

  // Derive the 1-hot encoding of the priority of the interrupt
  // currently being acknowledged.
  //
  irq_ack_w_1h      = `npuarc_IRQ_N'b0;
  // leda W71 off
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  case (irq_ack_w_r)
   `npuarc_IRQLGN_BITS'd0:
     irq_ack_w_1h[0] = 1'b1;
   `npuarc_IRQLGN_BITS'd1:
     irq_ack_w_1h[1] = 1'b1;
   `npuarc_IRQLGN_BITS'd2:
     irq_ack_w_1h[2] = 1'b1;
  endcase
  // leda DFT_022 on
  // leda W71 on

  icause_nxt        = irq_ack_num_r[`npuarc_IRQLGM16_RANGE]
                    ;

  icause_wen        = irq_ack_w_1h
                    & {`npuarc_IRQ_N{irq_ack_r}}
                    ;

  ar_aux_icause0_r = {
                          26'd0
                          , icause_0_r
                        }
                      ;
  ar_aux_icause1_r = {
                          26'd0
                          , icause_1_r
                        }
                      ;
  ar_aux_icause2_r = {
                          26'd0
                          , icause_2_r
                        }
                      ;

end // block: icause_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_interrupt_PROC: interrupt comb.                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
always @*
begin: irq_interrupt_PROC

  // AUX_IRQ_INTERRUPT (RW)
  //
  aux_irq_interrupt_en  = aux_irq_interrupt_sel;

  aux_irq_interrupt_nxt = aux_wdata[`npuarc_IRQLGM16_RANGE];

  // IRQ_LEVEL integer-to-one-hot decode.  Only those interrupt
  // numbers that correspond to an actual valid interrupt will be
  // decoded. All others will be ignored
  //
  // leda W71 off
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  aux_irq_interrupt_1h        = `npuarc_IRQ_M'b0;
  case (aux_irq_interrupt_r)
    `npuarc_IRQLGM16_BITS'd16: aux_irq_interrupt_1h[16] = 1'b1;
    `npuarc_IRQLGM16_BITS'd17: aux_irq_interrupt_1h[17] = 1'b1;
    `npuarc_IRQLGM16_BITS'd18: aux_irq_interrupt_1h[18] = 1'b1;
    `npuarc_IRQLGM16_BITS'd19: aux_irq_interrupt_1h[19] = 1'b1;
    `npuarc_IRQLGM16_BITS'd20: aux_irq_interrupt_1h[20] = 1'b1;
    `npuarc_IRQLGM16_BITS'd21: aux_irq_interrupt_1h[21] = 1'b1;
    `npuarc_IRQLGM16_BITS'd22: aux_irq_interrupt_1h[22] = 1'b1;
    `npuarc_IRQLGM16_BITS'd23: aux_irq_interrupt_1h[23] = 1'b1;
    `npuarc_IRQLGM16_BITS'd24: aux_irq_interrupt_1h[24] = 1'b1;
    `npuarc_IRQLGM16_BITS'd25: aux_irq_interrupt_1h[25] = 1'b1;
    `npuarc_IRQLGM16_BITS'd26: aux_irq_interrupt_1h[26] = 1'b1;
    `npuarc_IRQLGM16_BITS'd27: aux_irq_interrupt_1h[27] = 1'b1;
    `npuarc_IRQLGM16_BITS'd28: aux_irq_interrupt_1h[28] = 1'b1;
    `npuarc_IRQLGM16_BITS'd29: aux_irq_interrupt_1h[29] = 1'b1;
    `npuarc_IRQLGM16_BITS'd30: aux_irq_interrupt_1h[30] = 1'b1;
    `npuarc_IRQLGM16_BITS'd31: aux_irq_interrupt_1h[31] = 1'b1;
    `npuarc_IRQLGM16_BITS'd32: aux_irq_interrupt_1h[32] = 1'b1;
    `npuarc_IRQLGM16_BITS'd33: aux_irq_interrupt_1h[33] = 1'b1;
    `npuarc_IRQLGM16_BITS'd34: aux_irq_interrupt_1h[34] = 1'b1;
    `npuarc_IRQLGM16_BITS'd35: aux_irq_interrupt_1h[35] = 1'b1;
    `npuarc_IRQLGM16_BITS'd36: aux_irq_interrupt_1h[36] = 1'b1;
    `npuarc_IRQLGM16_BITS'd37: aux_irq_interrupt_1h[37] = 1'b1;
    `npuarc_IRQLGM16_BITS'd38: aux_irq_interrupt_1h[38] = 1'b1;
    `npuarc_IRQLGM16_BITS'd39: aux_irq_interrupt_1h[39] = 1'b1;
    `npuarc_IRQLGM16_BITS'd40: aux_irq_interrupt_1h[40] = 1'b1;
    `npuarc_IRQLGM16_BITS'd41: aux_irq_interrupt_1h[41] = 1'b1;
    `npuarc_IRQLGM16_BITS'd42: aux_irq_interrupt_1h[42] = 1'b1;
    `npuarc_IRQLGM16_BITS'd43: aux_irq_interrupt_1h[43] = 1'b1;
    `npuarc_IRQLGM16_BITS'd44: aux_irq_interrupt_1h[44] = 1'b1;
    `npuarc_IRQLGM16_BITS'd45: aux_irq_interrupt_1h[45] = 1'b1;
    `npuarc_IRQLGM16_BITS'd46: aux_irq_interrupt_1h[46] = 1'b1;
    `npuarc_IRQLGM16_BITS'd47: aux_irq_interrupt_1h[47] = 1'b1;
    `npuarc_IRQLGM16_BITS'd48: aux_irq_interrupt_1h[48] = 1'b1;
    `npuarc_IRQLGM16_BITS'd49: aux_irq_interrupt_1h[49] = 1'b1;
    `npuarc_IRQLGM16_BITS'd50: aux_irq_interrupt_1h[50] = 1'b1;
    `npuarc_IRQLGM16_BITS'd51: aux_irq_interrupt_1h[51] = 1'b1;
    `npuarc_IRQLGM16_BITS'd52: aux_irq_interrupt_1h[52] = 1'b1;
    `npuarc_IRQLGM16_BITS'd53: aux_irq_interrupt_1h[53] = 1'b1;
    `npuarc_IRQLGM16_BITS'd54: aux_irq_interrupt_1h[54] = 1'b1;
  endcase // case (aux_irq_interrupt_r)
  // leda DFT_022 on
  // leda W71 on

  // IRQ_PRIORITY_AUX (R/W)
  //
  aux_irq_priority_out   = `npuarc_DATA_SIZE'b0
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[16]}}
                                 & aux_irq_priority_16_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[17]}}
                                 & aux_irq_priority_17_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[18]}}
                                 & aux_irq_priority_18_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[19]}}
                                 & aux_irq_priority_19_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[20]}}
                                 & aux_irq_priority_20_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[21]}}
                                 & aux_irq_priority_21_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[22]}}
                                 & aux_irq_priority_22_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[23]}}
                                 & aux_irq_priority_23_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[24]}}
                                 & aux_irq_priority_24_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[25]}}
                                 & aux_irq_priority_25_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[26]}}
                                 & aux_irq_priority_26_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[27]}}
                                 & aux_irq_priority_27_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[28]}}
                                 & aux_irq_priority_28_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[29]}}
                                 & aux_irq_priority_29_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[30]}}
                                 & aux_irq_priority_30_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[31]}}
                                 & aux_irq_priority_31_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[32]}}
                                 & aux_irq_priority_32_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[33]}}
                                 & aux_irq_priority_33_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[34]}}
                                 & aux_irq_priority_34_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[35]}}
                                 & aux_irq_priority_35_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[36]}}
                                 & aux_irq_priority_36_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[37]}}
                                 & aux_irq_priority_37_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[38]}}
                                 & aux_irq_priority_38_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[39]}}
                                 & aux_irq_priority_39_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[40]}}
                                 & aux_irq_priority_40_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[41]}}
                                 & aux_irq_priority_41_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[42]}}
                                 & aux_irq_priority_42_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[43]}}
                                 & aux_irq_priority_43_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[44]}}
                                 & aux_irq_priority_44_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[45]}}
                                 & aux_irq_priority_45_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[46]}}
                                 & aux_irq_priority_46_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[47]}}
                                 & aux_irq_priority_47_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[48]}}
                                 & aux_irq_priority_48_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[49]}}
                                 & aux_irq_priority_49_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[50]}}
                                 & aux_irq_priority_50_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[51]}}
                                 & aux_irq_priority_51_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[52]}}
                                 & aux_irq_priority_52_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[53]}}
                                 & aux_irq_priority_53_r
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - `npuarc_IRQLGN_BITS){1'b0}}
                             , (   {`npuarc_IRQLGN_BITS{aux_irq_interrupt_1h[54]}}
                                 & aux_irq_priority_54_r
                               )
                           }
                         ;

  aux_irq_priority_en[16]= (   aux_irq_interrupt_1h[16]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[17]= (   aux_irq_interrupt_1h[17]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[18]= (   aux_irq_interrupt_1h[18]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[19]= (   aux_irq_interrupt_1h[19]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[20]= (   aux_irq_interrupt_1h[20]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[21]= (   aux_irq_interrupt_1h[21]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[22]= (   aux_irq_interrupt_1h[22]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[23]= (   aux_irq_interrupt_1h[23]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[24]= (   aux_irq_interrupt_1h[24]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[25]= (   aux_irq_interrupt_1h[25]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[26]= (   aux_irq_interrupt_1h[26]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[27]= (   aux_irq_interrupt_1h[27]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[28]= (   aux_irq_interrupt_1h[28]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[29]= (   aux_irq_interrupt_1h[29]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[30]= (   aux_irq_interrupt_1h[30]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[31]= (   aux_irq_interrupt_1h[31]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[32]= (   aux_irq_interrupt_1h[32]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[33]= (   aux_irq_interrupt_1h[33]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[34]= (   aux_irq_interrupt_1h[34]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[35]= (   aux_irq_interrupt_1h[35]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[36]= (   aux_irq_interrupt_1h[36]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[37]= (   aux_irq_interrupt_1h[37]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[38]= (   aux_irq_interrupt_1h[38]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[39]= (   aux_irq_interrupt_1h[39]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[40]= (   aux_irq_interrupt_1h[40]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[41]= (   aux_irq_interrupt_1h[41]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[42]= (   aux_irq_interrupt_1h[42]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[43]= (   aux_irq_interrupt_1h[43]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[44]= (   aux_irq_interrupt_1h[44]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[45]= (   aux_irq_interrupt_1h[45]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[46]= (   aux_irq_interrupt_1h[46]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[47]= (   aux_irq_interrupt_1h[47]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[48]= (   aux_irq_interrupt_1h[48]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[49]= (   aux_irq_interrupt_1h[49]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[50]= (   aux_irq_interrupt_1h[50]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[51]= (   aux_irq_interrupt_1h[51]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[52]= (   aux_irq_interrupt_1h[52]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[53]= (   aux_irq_interrupt_1h[53]
                             & aux_priority_sel
                           )
                         ;

  aux_irq_priority_en[54]= (   aux_irq_interrupt_1h[54]
                             & aux_priority_sel
                           )
                         ;

  // If Aux Priority is programmed incorrectly (greater than Max)
  // use Max priority

  aux_irq_priority_nxt   = ( ( |aux_wdata[`npuarc_IRQUNUSED_RANGE])
                           | ( {1'b0, aux_wdata[`npuarc_IRQLGN_RANGE]} > {1'b0, `npuarc_IRQLGN_BITS'd2} )  /* verilator lint_off CMPCONST */
                           )
                         ? `npuarc_IRQLGN_BITS'd2 :
                           aux_wdata[`npuarc_IRQLGN_RANGE]
                         ;

  // IRQ_ENABLE_AUX (RW)
  //
  aux_irq_enable_out     = `npuarc_DATA_SIZE'b0
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[16]
                                 & aux_irq_enable_r[16]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[17]
                                 & aux_irq_enable_r[17]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[18]
                                 & aux_irq_enable_r[18]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[19]
                                 & aux_irq_enable_r[19]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[20]
                                 & aux_irq_enable_r[20]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[21]
                                 & aux_irq_enable_r[21]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[22]
                                 & aux_irq_enable_r[22]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[23]
                                 & aux_irq_enable_r[23]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[24]
                                 & aux_irq_enable_r[24]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[25]
                                 & aux_irq_enable_r[25]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[26]
                                 & aux_irq_enable_r[26]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[27]
                                 & aux_irq_enable_r[27]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[28]
                                 & aux_irq_enable_r[28]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[29]
                                 & aux_irq_enable_r[29]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[30]
                                 & aux_irq_enable_r[30]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[31]
                                 & aux_irq_enable_r[31]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[32]
                                 & aux_irq_enable_r[32]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[33]
                                 & aux_irq_enable_r[33]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[34]
                                 & aux_irq_enable_r[34]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[35]
                                 & aux_irq_enable_r[35]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[36]
                                 & aux_irq_enable_r[36]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[37]
                                 & aux_irq_enable_r[37]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[38]
                                 & aux_irq_enable_r[38]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[39]
                                 & aux_irq_enable_r[39]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[40]
                                 & aux_irq_enable_r[40]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[41]
                                 & aux_irq_enable_r[41]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[42]
                                 & aux_irq_enable_r[42]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[43]
                                 & aux_irq_enable_r[43]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[44]
                                 & aux_irq_enable_r[44]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[45]
                                 & aux_irq_enable_r[45]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[46]
                                 & aux_irq_enable_r[46]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[47]
                                 & aux_irq_enable_r[47]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[48]
                                 & aux_irq_enable_r[48]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[49]
                                 & aux_irq_enable_r[49]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[50]
                                 & aux_irq_enable_r[50]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[51]
                                 & aux_irq_enable_r[51]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[52]
                                 & aux_irq_enable_r[52]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[53]
                                 & aux_irq_enable_r[53]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[54]
                                 & aux_irq_enable_r[54]
                               )
                           }
                         ;

  aux_irq_enable_en[16]  = (   aux_irq_interrupt_1h[16]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[17]  = (   aux_irq_interrupt_1h[17]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[18]  = (   aux_irq_interrupt_1h[18]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[19]  = (   aux_irq_interrupt_1h[19]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[20]  = (   aux_irq_interrupt_1h[20]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[21]  = (   aux_irq_interrupt_1h[21]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[22]  = (   aux_irq_interrupt_1h[22]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[23]  = (   aux_irq_interrupt_1h[23]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[24]  = (   aux_irq_interrupt_1h[24]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[25]  = (   aux_irq_interrupt_1h[25]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[26]  = (   aux_irq_interrupt_1h[26]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[27]  = (   aux_irq_interrupt_1h[27]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[28]  = (   aux_irq_interrupt_1h[28]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[29]  = (   aux_irq_interrupt_1h[29]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[30]  = (   aux_irq_interrupt_1h[30]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[31]  = (   aux_irq_interrupt_1h[31]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[32]  = (   aux_irq_interrupt_1h[32]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[33]  = (   aux_irq_interrupt_1h[33]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[34]  = (   aux_irq_interrupt_1h[34]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[35]  = (   aux_irq_interrupt_1h[35]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[36]  = (   aux_irq_interrupt_1h[36]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[37]  = (   aux_irq_interrupt_1h[37]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[38]  = (   aux_irq_interrupt_1h[38]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[39]  = (   aux_irq_interrupt_1h[39]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[40]  = (   aux_irq_interrupt_1h[40]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[41]  = (   aux_irq_interrupt_1h[41]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[42]  = (   aux_irq_interrupt_1h[42]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[43]  = (   aux_irq_interrupt_1h[43]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[44]  = (   aux_irq_interrupt_1h[44]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[45]  = (   aux_irq_interrupt_1h[45]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[46]  = (   aux_irq_interrupt_1h[46]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[47]  = (   aux_irq_interrupt_1h[47]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[48]  = (   aux_irq_interrupt_1h[48]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[49]  = (   aux_irq_interrupt_1h[49]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[50]  = (   aux_irq_interrupt_1h[50]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[51]  = (   aux_irq_interrupt_1h[51]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[52]  = (   aux_irq_interrupt_1h[52]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[53]  = (   aux_irq_interrupt_1h[53]
                             & aux_enable_sel
                           );
  aux_irq_enable_en[54]  = (   aux_irq_interrupt_1h[54]
                             & aux_enable_sel
                           );

  // IRQ_PULSE_CANCEL_AUX
  //
  aux_irq_pulse_cancel   = `npuarc_IRQ_E'b0;
  aux_irq_pulse_cancel[16] = (   aux_irq_interrupt_1h[16]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[17] = (   aux_irq_interrupt_1h[17]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[18] = (   aux_irq_interrupt_1h[18]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[19] = (   aux_irq_interrupt_1h[19]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[20] = (   aux_irq_interrupt_1h[20]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[21] = (   aux_irq_interrupt_1h[21]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[22] = (   aux_irq_interrupt_1h[22]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[23] = (   aux_irq_interrupt_1h[23]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[24] = (   aux_irq_interrupt_1h[24]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[25] = (   aux_irq_interrupt_1h[25]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[26] = (   aux_irq_interrupt_1h[26]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[27] = (   aux_irq_interrupt_1h[27]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[28] = (   aux_irq_interrupt_1h[28]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[29] = (   aux_irq_interrupt_1h[29]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[30] = (   aux_irq_interrupt_1h[30]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[31] = (   aux_irq_interrupt_1h[31]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[32] = (   aux_irq_interrupt_1h[32]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[33] = (   aux_irq_interrupt_1h[33]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[34] = (   aux_irq_interrupt_1h[34]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[35] = (   aux_irq_interrupt_1h[35]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[36] = (   aux_irq_interrupt_1h[36]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[37] = (   aux_irq_interrupt_1h[37]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[38] = (   aux_irq_interrupt_1h[38]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[39] = (   aux_irq_interrupt_1h[39]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[40] = (   aux_irq_interrupt_1h[40]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[41] = (   aux_irq_interrupt_1h[41]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[42] = (   aux_irq_interrupt_1h[42]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[43] = (   aux_irq_interrupt_1h[43]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[44] = (   aux_irq_interrupt_1h[44]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[45] = (   aux_irq_interrupt_1h[45]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[46] = (   aux_irq_interrupt_1h[46]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[47] = (   aux_irq_interrupt_1h[47]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[48] = (   aux_irq_interrupt_1h[48]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[49] = (   aux_irq_interrupt_1h[49]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[50] = (   aux_irq_interrupt_1h[50]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[51] = (   aux_irq_interrupt_1h[51]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[52] = (   aux_irq_interrupt_1h[52]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[53] = (   aux_irq_interrupt_1h[53]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;
  aux_irq_pulse_cancel[54] = (   aux_irq_interrupt_1h[54]
                               & aux_wdata0_r
                               & aux_irq_pulse_cancel_sel_r
                              )
                           ;

  // IRQ_TRIGGER
  //
  aux_irq_trigger_out    = `npuarc_DATA_SIZE'b0
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[16]
                                 & aux_irq_trigger_r[16]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[17]
                                 & aux_irq_trigger_r[17]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[18]
                                 & aux_irq_trigger_r[18]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[19]
                                 & aux_irq_trigger_r[19]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[20]
                                 & aux_irq_trigger_r[20]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[21]
                                 & aux_irq_trigger_r[21]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[22]
                                 & aux_irq_trigger_r[22]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[23]
                                 & aux_irq_trigger_r[23]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[24]
                                 & aux_irq_trigger_r[24]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[25]
                                 & aux_irq_trigger_r[25]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[26]
                                 & aux_irq_trigger_r[26]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[27]
                                 & aux_irq_trigger_r[27]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[28]
                                 & aux_irq_trigger_r[28]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[29]
                                 & aux_irq_trigger_r[29]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[30]
                                 & aux_irq_trigger_r[30]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[31]
                                 & aux_irq_trigger_r[31]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[32]
                                 & aux_irq_trigger_r[32]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[33]
                                 & aux_irq_trigger_r[33]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[34]
                                 & aux_irq_trigger_r[34]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[35]
                                 & aux_irq_trigger_r[35]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[36]
                                 & aux_irq_trigger_r[36]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[37]
                                 & aux_irq_trigger_r[37]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[38]
                                 & aux_irq_trigger_r[38]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[39]
                                 & aux_irq_trigger_r[39]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[40]
                                 & aux_irq_trigger_r[40]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[41]
                                 & aux_irq_trigger_r[41]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[42]
                                 & aux_irq_trigger_r[42]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[43]
                                 & aux_irq_trigger_r[43]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[44]
                                 & aux_irq_trigger_r[44]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[45]
                                 & aux_irq_trigger_r[45]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[46]
                                 & aux_irq_trigger_r[46]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[47]
                                 & aux_irq_trigger_r[47]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[48]
                                 & aux_irq_trigger_r[48]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[49]
                                 & aux_irq_trigger_r[49]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[50]
                                 & aux_irq_trigger_r[50]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[51]
                                 & aux_irq_trigger_r[51]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[52]
                                 & aux_irq_trigger_r[52]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[53]
                                 & aux_irq_trigger_r[53]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[54]
                                 & aux_irq_trigger_r[54]
                               )
                           }
                         ;

  aux_irq_trigger_en[16] = 1'b0;
  aux_irq_trigger_en[17] = (   aux_irq_interrupt_1h[17]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[18] = 1'b0;
  aux_irq_trigger_en[19] = (   aux_irq_interrupt_1h[19]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[20] = 1'b0;
  aux_irq_trigger_en[21] = (   aux_irq_interrupt_1h[21]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[22] = (   aux_irq_interrupt_1h[22]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[23] = (   aux_irq_interrupt_1h[23]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[24] = (   aux_irq_interrupt_1h[24]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[25] = (   aux_irq_interrupt_1h[25]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[26] = (   aux_irq_interrupt_1h[26]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[27] = (   aux_irq_interrupt_1h[27]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[28] = (   aux_irq_interrupt_1h[28]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[29] = (   aux_irq_interrupt_1h[29]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[30] = (   aux_irq_interrupt_1h[30]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[31] = (   aux_irq_interrupt_1h[31]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[32] = (   aux_irq_interrupt_1h[32]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[33] = (   aux_irq_interrupt_1h[33]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[34] = (   aux_irq_interrupt_1h[34]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[35] = (   aux_irq_interrupt_1h[35]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[36] = (   aux_irq_interrupt_1h[36]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[37] = (   aux_irq_interrupt_1h[37]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[38] = (   aux_irq_interrupt_1h[38]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[39] = (   aux_irq_interrupt_1h[39]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[40] = (   aux_irq_interrupt_1h[40]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[41] = (   aux_irq_interrupt_1h[41]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[42] = (   aux_irq_interrupt_1h[42]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[43] = (   aux_irq_interrupt_1h[43]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[44] = (   aux_irq_interrupt_1h[44]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[45] = (   aux_irq_interrupt_1h[45]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[46] = (   aux_irq_interrupt_1h[46]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[47] = (   aux_irq_interrupt_1h[47]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[48] = (   aux_irq_interrupt_1h[48]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[49] = (   aux_irq_interrupt_1h[49]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[50] = (   aux_irq_interrupt_1h[50]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[51] = (   aux_irq_interrupt_1h[51]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[52] = (   aux_irq_interrupt_1h[52]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[53] = (   aux_irq_interrupt_1h[53]
                                      & aux_trigger_sel
                                    );
  aux_irq_trigger_en[54] = (   aux_irq_interrupt_1h[54]
                                      & aux_trigger_sel
                                    );


  // IRQ_PENDING_AUX (R)
  //
  aux_irq_pending_out    = `npuarc_DATA_SIZE'b0
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[16]
                                 & aux_irq_pending[16]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[17]
                                 & aux_irq_pending[17]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[18]
                                 & aux_irq_pending[18]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[19]
                                 & aux_irq_pending[19]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[20]
                                 & aux_irq_pending[20]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[21]
                                 & aux_irq_pending[21]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[22]
                                 & aux_irq_pending[22]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[23]
                                 & aux_irq_pending[23]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[24]
                                 & aux_irq_pending[24]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[25]
                                 & aux_irq_pending[25]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[26]
                                 & aux_irq_pending[26]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[27]
                                 & aux_irq_pending[27]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[28]
                                 & aux_irq_pending[28]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[29]
                                 & aux_irq_pending[29]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[30]
                                 & aux_irq_pending[30]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[31]
                                 & aux_irq_pending[31]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[32]
                                 & aux_irq_pending[32]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[33]
                                 & aux_irq_pending[33]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[34]
                                 & aux_irq_pending[34]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[35]
                                 & aux_irq_pending[35]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[36]
                                 & aux_irq_pending[36]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[37]
                                 & aux_irq_pending[37]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[38]
                                 & aux_irq_pending[38]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[39]
                                 & aux_irq_pending[39]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[40]
                                 & aux_irq_pending[40]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[41]
                                 & aux_irq_pending[41]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[42]
                                 & aux_irq_pending[42]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[43]
                                 & aux_irq_pending[43]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[44]
                                 & aux_irq_pending[44]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[45]
                                 & aux_irq_pending[45]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[46]
                                 & aux_irq_pending[46]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[47]
                                 & aux_irq_pending[47]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[48]
                                 & aux_irq_pending[48]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[49]
                                 & aux_irq_pending[49]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[50]
                                 & aux_irq_pending[50]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[51]
                                 & aux_irq_pending[51]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[52]
                                 & aux_irq_pending[52]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[53]
                                 & aux_irq_pending[53]
                               )
                           }
                         | {   {(`npuarc_DATA_SIZE - 1){1'b0}}
                             , (   aux_irq_interrupt_1h[54]
                                 & aux_irq_pending[54]
                               )
                           }
                         ;

  // IRQ_STATUS_AUX (R)
  //
  aux_irq_status_out = `npuarc_DATA_SIZE'b0;
  aux_irq_status_out[31]     = aux_irq_pending_out[0];
  aux_irq_status_out[5]     = aux_irq_trigger_out[0];
  aux_irq_status_out[4]     = aux_irq_enable_out[0];
  aux_irq_status_out[`npuarc_IRQLGN_RANGE]     = aux_irq_priority_out[`npuarc_IRQLGN_RANGE];

end // block: irq_interrupt_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_aux_rdata_PROC: irq_aux_rdata output MUX                                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_aux_rdata_PROC

  irq_aux_rdata         = `npuarc_DATA_SIZE'd0;
  rdata_unimpl          = 1'b0;

  // Mux the IRQ-related AUX registers to produce irq_aux_rdata. This
  // logic is partitioned into a seperate 'always' block to prevent
  // simulation mismatches between VCS and Modelsim.
  //
  case (qual_aux_addr)
    `npuarc_IRQ_PRIORITY_AUX:
      irq_aux_rdata     = `npuarc_DATA_SIZE'd0
                    | aux_irq_priority_out
                    ;
    `npuarc_IRQ_PENDING_AUX:
      irq_aux_rdata     = aux_irq_pending_out;
    `npuarc_IRQ_ENABLE_AUX:
      irq_aux_rdata     = aux_irq_enable_out;
    `npuarc_IRQ_TRIGGER_AUX:
      irq_aux_rdata     = aux_irq_trigger_out;
    `npuarc_IRQ_STATUS_AUX:
      irq_aux_rdata     = aux_irq_status_out;
    default: begin
      irq_aux_rdata     = base_rdata;

      rdata_unimpl      = 1'b1;
    end
  endcase

  // The AUX is unimplemented when we have not hit an address in
  // either the base or data decode units.
  //
  irq_aux_unimpl        = base_unimpl & rdata_unimpl
                     ;

end // block: irq_aux_rdata_PROC

//////////////////////////////////////////////////////////////////////////// 
//                                                                        //
// @irq_ack_r_PROC                                                        //
////////////////////////////////////////////////////////////////////////////
//we flop irq_ack and it's acked irq_num (irq_ack_num) to solve timing issues
//
always @(posedge clk or posedge rst_a)
begin: irq_ack_r_PROC
  if (rst_a == 1'b1) begin
    irq_ack_r <= 1'b0;
  end
  else begin
    irq_ack_r <= irq_ack;
  end
end

always @(posedge clk or posedge rst_a)
begin: irq_ack_num_r_PROC
  if (rst_a == 1'b1) begin
    irq_ack_num_r <= 8'b0;
  end
  else if (irq_ack) begin
    irq_ack_num_r <= irq_ack_num;
  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @update_ctl_PROC: register update control 
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// 1. IRQ output uses the irq sample clock, it guarantees irq_r/timer timing
// 2. aux register write (except aux_interrupt register) needs a wait cycle
//    to guarantees aux register timing
// 3. pulse interrupt cancel, aux_irq_pulse_cancel_sel_r, needs a wait cycle 
//    it affects pending_r (see pending_update)
// 4. irq_ack needs a wait cycle
//    it affects irq_ack_r and irq_ack_num_r -> pending_r
// 5. irq_ack_r that is used in irq_unit logic needs a wait cycle
//    it affects pending_r (see pending_update)
//
always @(posedge clk or posedge rst_a)
begin: update_ctl_PROC
  if (rst_a == 1'b1) begin
    aux_irq_update_kill        <= 1'b0;
    irq_ack_update_kill        <= 1'b0;
    aux_irq_pulse_cancel_sel_r <= 1'b0;
    aux_wdata0_r               <= 1'b0;
  end
  else begin
    aux_irq_update_kill        <= aux_irq_ctl_sel                               // (2) 
                               | aux_irq_pulse_cancel_sel_r                     // (3)
                               ;
    irq_ack_update_kill        <= irq_ack | irq_ack_r;                          // (4,5)
    aux_irq_pulse_cancel_sel_r <= aux_irq_pulse_cancel_sel;
    aux_wdata0_r               <= aux_wdata[0];
  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_reg_PROC: Per-CPU Auxiliary registers                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: irq_hint_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_irq_hint_r      <= `npuarc_IRQLGM16_BITS'b0;
  end
  else if (aux_irq_hint_en == 1'b1) begin
    aux_irq_hint_r      <= aux_wdata[`npuarc_IRQLGM16_RANGE];
  end
end // block: irq_reg_PROC

always @(posedge clk or posedge rst_a)
begin: irq_interrupt_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_interrupt_r <= `npuarc_IRQLGM16_BITS'b0;
  end
  else if (aux_irq_interrupt_en == 1'b1) begin
    aux_irq_interrupt_r <= aux_irq_interrupt_nxt;
  end
end // block: irq_reg_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_level_reg_PROC: Common IRQ auxiliary registers                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low 
// SJ:  Done on purpose


wire [`npuarc_IRQLGN_RANGE]      aux_irq_priority_r [`npuarc_IRQM_RANGE];

always @(posedge clk or posedge rst_a)
begin: irq_priority_54_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_54_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[54] == 1'b1)) begin
    // IRQ:54
    aux_irq_priority_54_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_54_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_53_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_53_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[53] == 1'b1)) begin
    // IRQ:53
    aux_irq_priority_53_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_53_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_52_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_52_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[52] == 1'b1)) begin
    // IRQ:52
    aux_irq_priority_52_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_52_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_51_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_51_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[51] == 1'b1)) begin
    // IRQ:51
    aux_irq_priority_51_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_51_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_50_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_50_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[50] == 1'b1)) begin
    // IRQ:50
    aux_irq_priority_50_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_50_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_49_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_49_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[49] == 1'b1)) begin
    // IRQ:49
    aux_irq_priority_49_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_49_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_48_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_48_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[48] == 1'b1)) begin
    // IRQ:48
    aux_irq_priority_48_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_48_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_47_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_47_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[47] == 1'b1)) begin
    // IRQ:47
    aux_irq_priority_47_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_47_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_46_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_46_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[46] == 1'b1)) begin
    // IRQ:46
    aux_irq_priority_46_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_46_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_45_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_45_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[45] == 1'b1)) begin
    // IRQ:45
    aux_irq_priority_45_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_45_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_44_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_44_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[44] == 1'b1)) begin
    // IRQ:44
    aux_irq_priority_44_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_44_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_43_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_43_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[43] == 1'b1)) begin
    // IRQ:43
    aux_irq_priority_43_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_43_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_42_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_42_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[42] == 1'b1)) begin
    // IRQ:42
    aux_irq_priority_42_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_42_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_41_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_41_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[41] == 1'b1)) begin
    // IRQ:41
    aux_irq_priority_41_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_41_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_40_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_40_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[40] == 1'b1)) begin
    // IRQ:40
    aux_irq_priority_40_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_40_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_39_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_39_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[39] == 1'b1)) begin
    // IRQ:39
    aux_irq_priority_39_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_39_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_38_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_38_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[38] == 1'b1)) begin
    // IRQ:38
    aux_irq_priority_38_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_38_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_37_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_37_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[37] == 1'b1)) begin
    // IRQ:37
    aux_irq_priority_37_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_37_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_36_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_36_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[36] == 1'b1)) begin
    // IRQ:36
    aux_irq_priority_36_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_36_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_35_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_35_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[35] == 1'b1)) begin
    // IRQ:35
    aux_irq_priority_35_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_35_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_34_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_34_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[34] == 1'b1)) begin
    // IRQ:34
    aux_irq_priority_34_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_34_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_33_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_33_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[33] == 1'b1)) begin
    // IRQ:33
    aux_irq_priority_33_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_33_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_32_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_32_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[32] == 1'b1)) begin
    // IRQ:32
    aux_irq_priority_32_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_32_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_31_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_31_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[31] == 1'b1)) begin
    // IRQ:31
    aux_irq_priority_31_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_31_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_30_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_30_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[30] == 1'b1)) begin
    // IRQ:30
    aux_irq_priority_30_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_30_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_29_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_29_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[29] == 1'b1)) begin
    // IRQ:29
    aux_irq_priority_29_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_29_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_28_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_28_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[28] == 1'b1)) begin
    // IRQ:28
    aux_irq_priority_28_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_28_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_27_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_27_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[27] == 1'b1)) begin
    // IRQ:27
    aux_irq_priority_27_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_27_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_26_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_26_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[26] == 1'b1)) begin
    // IRQ:26
    aux_irq_priority_26_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_26_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_25_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_25_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[25] == 1'b1)) begin
    // IRQ:25
    aux_irq_priority_25_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_25_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_24_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_24_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[24] == 1'b1)) begin
    // IRQ:24
    aux_irq_priority_24_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_24_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_23_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_23_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[23] == 1'b1)) begin
    // IRQ:23
    aux_irq_priority_23_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_23_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_22_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_22_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[22] == 1'b1)) begin
    // IRQ:22
    aux_irq_priority_22_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_22_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_21_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_21_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[21] == 1'b1)) begin
    // IRQ:21
    aux_irq_priority_21_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_21_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_20_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_20_r    <= `npuarc_IRQLGN_BITS'd1;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[20] == 1'b1)) begin
    // IRQ:20
    aux_irq_priority_20_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_20_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_19_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_19_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[19] == 1'b1)) begin
    // IRQ:19
    aux_irq_priority_19_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_19_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_18_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_18_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[18] == 1'b1)) begin
    // IRQ:18
    aux_irq_priority_18_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_18_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_17_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_17_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[17] == 1'b1)) begin
    // IRQ:17
    aux_irq_priority_17_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_17_reg_PROC
always @(posedge clk or posedge rst_a)
begin: irq_priority_16_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_priority_16_r    <= `npuarc_IRQLGN_BITS'd0;
  end
  else if ((aux_irq_wen_r == 1'b1) && (aux_irq_priority_en[16] == 1'b1)) begin
    // IRQ:16
    aux_irq_priority_16_r  <= aux_irq_priority_nxt;
  end
end // block:  irq_priority_16_reg_PROC

wire [`npuarc_IRQM_RANGE] aux_irq_enable_nxt;
assign aux_irq_enable_nxt = {
  (aux_irq_enable_en[54] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[54],
  (aux_irq_enable_en[53] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[53],
  (aux_irq_enable_en[52] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[52],
  (aux_irq_enable_en[51] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[51],
  (aux_irq_enable_en[50] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[50],
  (aux_irq_enable_en[49] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[49],
  (aux_irq_enable_en[48] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[48],
  (aux_irq_enable_en[47] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[47],
  (aux_irq_enable_en[46] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[46],
  (aux_irq_enable_en[45] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[45],
  (aux_irq_enable_en[44] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[44],
  (aux_irq_enable_en[43] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[43],
  (aux_irq_enable_en[42] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[42],
  (aux_irq_enable_en[41] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[41],
  (aux_irq_enable_en[40] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[40],
  (aux_irq_enable_en[39] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[39],
  (aux_irq_enable_en[38] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[38],
  (aux_irq_enable_en[37] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[37],
  (aux_irq_enable_en[36] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[36],
  (aux_irq_enable_en[35] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[35],
  (aux_irq_enable_en[34] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[34],
  (aux_irq_enable_en[33] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[33],
  (aux_irq_enable_en[32] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[32],
  (aux_irq_enable_en[31] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[31],
  (aux_irq_enable_en[30] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[30],
  (aux_irq_enable_en[29] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[29],
  (aux_irq_enable_en[28] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[28],
  (aux_irq_enable_en[27] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[27],
  (aux_irq_enable_en[26] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[26],
  (aux_irq_enable_en[25] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[25],
  (aux_irq_enable_en[24] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[24],
  (aux_irq_enable_en[23] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[23],
  (aux_irq_enable_en[22] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[22],
  (aux_irq_enable_en[21] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[21],
  (aux_irq_enable_en[20] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[20],
  (aux_irq_enable_en[19] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[19],
  (aux_irq_enable_en[18] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[18],
  (aux_irq_enable_en[17] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[17],
  (aux_irq_enable_en[16] == 1'b1) ? aux_wdata[0] : aux_irq_enable_r[16]
};

wire [`npuarc_IRQE_RANGE] aux_irq_trigger_nxt;
assign aux_irq_trigger_nxt = {
  (aux_irq_trigger_en[54] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[54],
  (aux_irq_trigger_en[53] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[53],
  (aux_irq_trigger_en[52] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[52],
  (aux_irq_trigger_en[51] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[51],
  (aux_irq_trigger_en[50] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[50],
  (aux_irq_trigger_en[49] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[49],
  (aux_irq_trigger_en[48] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[48],
  (aux_irq_trigger_en[47] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[47],
  (aux_irq_trigger_en[46] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[46],
  (aux_irq_trigger_en[45] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[45],
  (aux_irq_trigger_en[44] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[44],
  (aux_irq_trigger_en[43] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[43],
  (aux_irq_trigger_en[42] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[42],
  (aux_irq_trigger_en[41] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[41],
  (aux_irq_trigger_en[40] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[40],
  (aux_irq_trigger_en[39] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[39],
  (aux_irq_trigger_en[38] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[38],
  (aux_irq_trigger_en[37] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[37],
  (aux_irq_trigger_en[36] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[36],
  (aux_irq_trigger_en[35] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[35],
  (aux_irq_trigger_en[34] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[34],
  (aux_irq_trigger_en[33] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[33],
  (aux_irq_trigger_en[32] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[32],
  (aux_irq_trigger_en[31] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[31],
  (aux_irq_trigger_en[30] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[30],
  (aux_irq_trigger_en[29] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[29],
  (aux_irq_trigger_en[28] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[28],
  (aux_irq_trigger_en[27] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[27],
  (aux_irq_trigger_en[26] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[26],
  (aux_irq_trigger_en[25] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[25],
  (aux_irq_trigger_en[24] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[24],
  (aux_irq_trigger_en[23] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[23],
  (aux_irq_trigger_en[22] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[22],
  (aux_irq_trigger_en[21] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[21],
  (aux_irq_trigger_en[20] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[20],
  (aux_irq_trigger_en[19] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[19],
  (aux_irq_trigger_en[18] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[18],
  (aux_irq_trigger_en[17] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[17],
  (aux_irq_trigger_en[16] == 1'b1) ? aux_wdata[0] : aux_irq_trigger_r[16]
};

always @(posedge clk or posedge rst_a)
begin: irq_enable_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_enable_r <= {`npuarc_IRQ_M{1'b1}};
  end
  else if (aux_irq_wen_r == 1'b1) begin
    aux_irq_enable_r <= aux_irq_enable_nxt;
  end
end // block: irq_level_reg_PROC

always @(posedge clk or posedge rst_a)
begin: irq_trigger_reg_PROC
  if (rst_a == 1'b1) begin
    aux_irq_trigger_r <= `npuarc_IRQ_E'b0;
  end
  else if (aux_irq_wen_r == 1'b1) begin
    aux_irq_trigger_r <= aux_irq_trigger_nxt;
  end
end // block: irq_level_reg_PROC

// spyglass enable_block FlopEConst
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @icause_reg_PROC: Architectural ICAUSE registers                       //
// icause_r registers are localized in the irq unit.                      //
// irq_l_comb_r identifies active interrupts on each irq priority level   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: icause_0_reg_PROC
  if (rst_a == 1'b1) begin
    icause_0_r <= `npuarc_IRQLGM16_BITS'b0;
  end
  else if (icause_wen[0] == 1'b1) begin
    icause_0_r <= icause_nxt;
  end
end // block: icause_reg_PROC
always @(posedge clk or posedge rst_a)
begin: icause_1_reg_PROC
  if (rst_a == 1'b1) begin
    icause_1_r <= `npuarc_IRQLGM16_BITS'b0;
  end
  else if (icause_wen[1] == 1'b1) begin
    icause_1_r <= icause_nxt;
  end
end // block: icause_reg_PROC
always @(posedge clk or posedge rst_a)
begin: icause_2_reg_PROC
  if (rst_a == 1'b1) begin
    icause_2_r <= `npuarc_IRQLGM16_BITS'b0;
  end
  else if (icause_wen[2] == 1'b1) begin
    icause_2_r <= icause_nxt;
  end
end // block: icause_reg_PROC

// leda W563 off
      // LMD: Reduction of single bit expression is redundant
      // LJ: configurable field may be a single bit
// spyglass disable_block Ac_conv02
// SMD: cdc sync signals converging on combinational gate
// SJ:  cdc syncs are independent and chance of glitch is very low
wire [`npuarc_IRQN_RANGE] irq_l_comb_nxt;
assign irq_l_comb_nxt = {
  |irq_l_2,
  |irq_l_1,
  |irq_l_0
};
// spyglass enable_block Ac_conv02
// leda W563 on

always @(posedge clk or posedge rst_a)
begin: irq_l_comb_reg_PROC
  if (rst_a == 1'b1) begin
    irq_l_comb_r <= `npuarc_IRQ_N'b0;
  end
  else begin
    irq_l_comb_r <= irq_l_comb_nxt;
  end
end // block: icause_reg_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @pending_reg_PROC: Non-architectural (internal) registers              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: pending_reg_PROC
  if (rst_a == 1'b1) begin
    pending_r       <= `npuarc_IRQ_E'b0;
    pending_clear_r <= 1'b0;
  end
  else if (pending_update) begin
    pending_r       <= pending_nxt;
    pending_clear_r <= pending_clear_nxt;
  end
end // block: pending_reg_PROC
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @edge_reg_PROC: "edge transition detector"-register                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

wire [`npuarc_IRQE_RANGE] irq_edge_inter = {
  ( (irq_edge_en[54] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[54] : irq_edge_r[54],
  ( (irq_edge_en[53] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[53] : irq_edge_r[53],
  ( (irq_edge_en[52] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[52] : irq_edge_r[52],
  ( (irq_edge_en[51] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[51] : irq_edge_r[51],
  ( (irq_edge_en[50] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[50] : irq_edge_r[50],
  ( (irq_edge_en[49] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[49] : irq_edge_r[49],
  ( (irq_edge_en[48] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[48] : irq_edge_r[48],
  ( (irq_edge_en[47] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[47] : irq_edge_r[47],
  ( (irq_edge_en[46] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[46] : irq_edge_r[46],
  ( (irq_edge_en[45] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[45] : irq_edge_r[45],
  ( (irq_edge_en[44] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[44] : irq_edge_r[44],
  ( (irq_edge_en[43] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[43] : irq_edge_r[43],
  ( (irq_edge_en[42] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[42] : irq_edge_r[42],
  ( (irq_edge_en[41] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[41] : irq_edge_r[41],
  ( (irq_edge_en[40] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[40] : irq_edge_r[40],
  ( (irq_edge_en[39] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[39] : irq_edge_r[39],
  ( (irq_edge_en[38] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[38] : irq_edge_r[38],
  ( (irq_edge_en[37] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[37] : irq_edge_r[37],
  ( (irq_edge_en[36] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[36] : irq_edge_r[36],
  ( (irq_edge_en[35] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[35] : irq_edge_r[35],
  ( (irq_edge_en[34] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[34] : irq_edge_r[34],
  ( (irq_edge_en[33] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[33] : irq_edge_r[33],
  ( (irq_edge_en[32] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[32] : irq_edge_r[32],
  ( (irq_edge_en[31] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[31] : irq_edge_r[31],
  ( (irq_edge_en[30] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[30] : irq_edge_r[30],
  ( (irq_edge_en[29] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[29] : irq_edge_r[29],
  ( (irq_edge_en[28] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[28] : irq_edge_r[28],
  ( (irq_edge_en[27] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[27] : irq_edge_r[27],
  ( (irq_edge_en[26] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[26] : irq_edge_r[26],
  ( (irq_edge_en[25] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[25] : irq_edge_r[25],
  ( (irq_edge_en[24] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[24] : irq_edge_r[24],
  ( (irq_edge_en[23] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[23] : irq_edge_r[23],
  ( (irq_edge_en[22] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[22] : irq_edge_r[22],
  ( (irq_edge_en[21] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[21] : irq_edge_r[21],
  ( (irq_edge_en[20] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[20] : irq_edge_r[20],
  ( (irq_edge_en[19] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[19] : irq_edge_r[19],
  ( (irq_edge_en[18] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[18] : irq_edge_r[18],
  ( (irq_edge_en[17] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[17] : irq_edge_r[17],
  ( (irq_edge_en[16] == 1'b1) 
       & irq_clk_en_r
  ) ? irq_edge_nxt[16] : irq_edge_r[16]
};

always @(posedge clk or posedge rst_a)
begin: edge_reg_PROC
  if (rst_a == 1'b1) begin
    irq_edge_r <= `npuarc_IRQ_E'b0;
  end
  else begin
    irq_edge_r <= irq_edge_inter;
  end
end // block: edge_reg_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @out_reg_PROC: Output retiming register for large IRQ_N                //
// The irq outputs are sampled by a 2 cycle clock enable irq_clk_en       //
// The first cycle (when irq_clk_en=0) signal should not be used          // 
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
// spyglass disable_block ImproperRangeIndex-ML
// SMD: OutOfRangeIndex
// SJ: Index values are always in Range
always @(posedge clk or posedge rst_a)
begin: irq_preempts_reg_PROC
  if (rst_a == 1'b1) begin
    irq_preempts_r  <= 1'b0;
  end
  else if ((irq_clk_en_r & (~(aux_irq_update_kill | irq_ack_update_kill))) | irq_ack) begin
    irq_preempts_r  <= irq_ack ? 1'b0 : (irq_preempts_pre & cpu_accept_irq[irq_w_nxt]);
  end
end
// spyglass enable_block ImproperRangeIndex-ML                      

always @(posedge clk or posedge rst_a)
begin: out_reg_PROC
  if (rst_a == 1'b1) begin
    irq_req_r       <= 1'b0;
    irq_num_r       <= 8'b0;
    irq_w_r         <= `npuarc_IRQLGN_BITS'd0;
  end
  else if (irq_clk_en_r & (~(aux_irq_update_kill | irq_ack_update_kill))) begin
    irq_req_r       <= irq_req_nxt;
    irq_w_r         <= irq_w_nxt;
    irq_num_r       <= (|irq_num_r & !(|irq_num_nxt)) ? irq_num_r : irq_num_nxt;
  end
end


// spyglass disable_block ImproperRangeIndex-ML
// SMD: OutOfRangeIndex
// SJ: Index values are always in Range
assign irq_preempts_nxt = irq_preempts_pre & cpu_accept_irq[irq_w_nxt];
// spyglass enable_block ImproperRangeIndex-ML                      

wire [`npuarc_IRQM_RANGE]        irq_l [`npuarc_IRQN_RANGE];
wire [`npuarc_IRQM_RANGE]        irq_lbitmap [`npuarc_IRQN_RANGE];
assign irq_l [0]       = irq_l_0 ;
assign irq_lbitmap [0] = irq_lbitmap_0 ;

assign irq_l [1]       = irq_l_1 ;
assign irq_lbitmap [1] = irq_lbitmap_1 ;

assign irq_l [2]       = irq_l_2 ;
assign irq_lbitmap [2] = irq_lbitmap_2 ;




endmodule // alb_irq_unit
