// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2013 Synopsys, Inc. All rights reserved.
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
// ######  #######  #####
// #     #    #    #     #
// #     #    #    #
// ######     #    #
// #   #      #    #
// #    #     #    #     #
// #     #    #     #####
//
// ===========================================================================
//
// Description:
//
//  This module implements the Real-Time Clock (RTC) of the ARCv2HS CPU.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_rtc (

  ////////// Interface for SR instructions to write aux regs ///////////////
  //
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r,     // Aux write data
  // leda NTL_CON13C on
  input                       aux_read,         // Aux Read  Operation
  input                       aux_write,        // Aux Write Operation
  input                       aux_rtc_ren_r,    // Aux region select for Read
  input      [2:0]            aux_rtc_raddr_r,  // Aux address for Read
  input                       aux_rtc_wen_r,    // Aux region select for Write
  input      [2:0]            aux_rtc_waddr_r,  // Aux address for Write

  output reg [`npuarc_DATA_RANGE]    rtc_aux_rdata,     // LR read data
  output reg                  rtc_aux_illegal,   // SR/LR operation is illegal
  output reg                  rtc_aux_k_rd,      // op needs Kernel R perm
  output reg                  rtc_aux_k_wr,      // op needs Kernel W perm
  output reg                  rtc_aux_unimpl,    // LR/SR reg is not present
  output reg                  rtc_aux_serial_sr, // SR needs Serialization
  output reg                  rtc_aux_strict_sr, // SR must Serialize

  /////////// Processor-side Interrupt Interface ///////////////////////////
  //
  input                       rtc_na,        // RTC Non-atomic

  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,           // Clock
  input                       rst_a          // ASync. reset
  );

// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Signal/Register Declerations                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// aux_PROC
//
reg                      rtc_read_lo;
reg                      rtc_read_hi;
reg                      rtc_ctrl_w;
reg                      rtc_ctrl_r;



// rtc_PROC
//
reg                      rtc_clear;
reg [`npuarc_RTC_RANGE]         rtc_count_nxt;
reg                      rtc_count_en;
reg                      rtc_non_atomic;
reg [`npuarc_DATA_RANGE]        ar_aux_rtc_ctrl;
reg                      aux_rtc_ctrl_e_nxt;

// rtc_a01_nxt_PROC
//
reg                      rtc_a0_nxt;
reg                      rtc_a1_nxt;
reg                      rtc_ctrl_rw;

// rtc_reg_PROC
//
reg                      aux_rtc_ctrl_e_r;
reg [`npuarc_RTC_RANGE]         rtc_count_r;
reg                      rtc_a0_r;
reg                      rtc_a1_r;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @aux_PROC: Auxiliary register decode comb.                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: aux_PROC

  // AUX bus output.
  //
  rtc_aux_rdata      = `npuarc_DATA_SIZE'd0;
  rtc_aux_k_rd       = 1'b0;
  rtc_aux_k_wr       = 1'b0;
  rtc_aux_unimpl     = 1'b1;
  rtc_aux_illegal    = 1'b0;
  rtc_aux_serial_sr  = 1'b0;
  rtc_aux_strict_sr  = 1'b0;

  // RTC register enables
  //
  rtc_read_lo       = 1'b0;
  rtc_read_hi       = 1'b0;
  rtc_ctrl_r        = 1'b0;

  if (aux_rtc_ren_r == 1'b1)
  begin
    rtc_aux_unimpl          = 1'b0;
    case ({8'h10, 1'b0, aux_rtc_raddr_r})
      `npuarc_RTC_CTRL_AUX: 
      begin
        rtc_aux_rdata       = ar_aux_rtc_ctrl;
        rtc_aux_k_wr        = aux_write;
        rtc_aux_strict_sr   = aux_write;

        rtc_ctrl_r          = aux_read;
      end

      `npuarc_RTC_LOW_AUX: 
      begin
        rtc_aux_rdata       = rtc_count_r[31:0];
        rtc_aux_illegal     = aux_write;

        rtc_read_lo         = aux_read;
      end

      `npuarc_RTC_HIGH_AUX: 
      begin
        rtc_aux_rdata       = rtc_count_r[63:32];
        rtc_aux_illegal     = aux_write;

        rtc_read_hi         = aux_read;
      end
      default: 
      begin
        rtc_aux_unimpl      = 1'b1;
      end

    endcase // case (qual_aux_addr)
  end // if (aux_rtc_ren_r == 1'b1)
end // block: aux_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting an SR                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rtc_aux_wen_PROC
  rtc_ctrl_w        = 1'b0;
  if (aux_rtc_wen_r == 1'b1)
    case ({8'h10, 1'b0, aux_rtc_waddr_r})
      `npuarc_RTC_CTRL_AUX :  rtc_ctrl_w  = 1'b1;
      default:  ;
    endcase
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @rtc_PROC: Real-Time Clock comb.                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: rtc_PROC

  // Clear the RTC when writing to the 'C' bit in the control
  // register.
  //
  rtc_clear         = rtc_ctrl_w
                    & wa_sr_data_r[`npuarc_RTC_C]
                    ;

  // Implement the counter.
  //
  // leda W484 off
  // LMD: Possible loss of carry/borrow in add/sub
  // LJ:  RTC is wrap around counter
  //      Carry bit is redundant
  // leda BTTF_D002 off
  // LMD: Unequal LHS and RHS
  // LJ: Carry bit is redundant  
  rtc_count_nxt     = (rtc_clear == 1'b1)
                    ? `npuarc_RTC_BITS'b0
                    : rtc_count_r + `npuarc_RTC_BITS'd1
                    ;
  // leda BTTF_D002 on
  // leda W484 on

  // Update count when the counter is enabled.
  //
  rtc_count_en      = rtc_clear
                    | aux_rtc_ctrl_e_r
                    ;

  // The transaction to the RTC is not atomic when the upper 32-bits
  // has been incremented between reads to Hi and Lo, when an
  // interrupt has taken place, or when an exception has taken
  // place. Compare the value of count_nxt such that rtc_non_atomic
  // will be asserted the cycle before the hi changes to coincide with
  // the change in rtc_a[01].
  //
  rtc_non_atomic    = (rtc_count_nxt[63:32] != rtc_count_r[63:32])
                    | rtc_na
                    ;

  // RTC_CTRL
  //
  aux_rtc_ctrl_e_nxt = wa_sr_data_r[`npuarc_RTC_EN];

  // Architectural RTC_CTRL register. Implicitly assume that
  // the 'C'-bit is write-only and returns zero on read.
  //
  ar_aux_rtc_ctrl   = {   rtc_a1_r
                        , rtc_a0_r
                        , `npuarc_RTC_CTRL_UNUSED'd0
                        , 1'b0
                        , aux_rtc_ctrl_e_r
                      }
                    ;

end // block: rtc_PROC

always @*
begin: rtc_a01_nxt_PROC

  rtc_ctrl_rw = (rtc_ctrl_w | rtc_ctrl_r);

  casez ( {rtc_ctrl_rw, rtc_a1_r, rtc_a0_r} )
    3'b1_??: begin
      rtc_a0_nxt = 1'b0;
      rtc_a1_nxt = 1'b0;
    end
    3'b0_00: begin
      rtc_a0_nxt = rtc_read_lo & (~rtc_non_atomic);
      rtc_a1_nxt = rtc_a1_r;
    end
    3'b0_11: begin
      rtc_a0_nxt = ~(rtc_ctrl_w | rtc_ctrl_r | rtc_non_atomic);
      rtc_a1_nxt = ~(rtc_read_lo & (~rtc_non_atomic))
                 & (~(rtc_ctrl_w | rtc_ctrl_r | rtc_non_atomic));
    end
    3'b0_01: begin
      rtc_a0_nxt = ~(rtc_ctrl_w | rtc_ctrl_r | rtc_non_atomic);
      rtc_a1_nxt =   rtc_read_hi & (~rtc_non_atomic);
    end
    default: begin
      rtc_a0_nxt = rtc_a0_r;
      rtc_a1_nxt = rtc_a1_r;
    end
  endcase // casez ( {rtc_ctrl_w, rtc_a0_r, rtc_a1_r} )
end // block: rtc_a01_nxt_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @rtc_reg_PROC: RTC registers                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: rtc_ctrl_reg_PROC
  if (rst_a == 1'b1)
    aux_rtc_ctrl_e_r <= 1'b0;
  else if( rtc_ctrl_w == 1'b1 )
    aux_rtc_ctrl_e_r <= aux_rtc_ctrl_e_nxt;
end // block: rtc_reg_PROC

always @(posedge clk or posedge rst_a)
begin: rtc_count_reg_PROC
  if (rst_a == 1'b1)
    rtc_count_r      <= 64'b0;
  else if( rtc_count_en == 1'b1 )
    rtc_count_r    <= rtc_count_nxt;
end // block: rtc_reg_PROC

always @(posedge clk or posedge rst_a)
begin: rtc_reg_PROC
  if (rst_a == 1'b1) begin
    rtc_a0_r         <= 1'b0;
    rtc_a1_r         <= 1'b0;
  end
  else begin
    rtc_a0_r         <= rtc_a0_nxt;
    rtc_a1_r         <= rtc_a1_nxt;
  end
end // block: rtc_reg_PROC

// spyglass enable_block W193

endmodule // alb_rtc
