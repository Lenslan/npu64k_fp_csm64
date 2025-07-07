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
//   #####     #    #    #  ######  #####    ####
//     #       #    ##  ##  #       #    #  #
//     #       #    # ## #  #####   #    #   ####
//     #       #    #    #  #       #####        #
//     #       #    #    #  #       #   #   #    #
//     #       #    #    #  ######  #    #   ####
//
// ===========================================================================
//
// Description:
//
//  This module implements the timers of for ARCv2HS CPU.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_timers (
  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,
  input                       rst_a,
  output                      timer_unit_enable, 

  ////////// General input signals /////////////////////////////////////////
  //
  input                       db_active,     // Host debug op in progress
  input                       sys_halt_r,    // halted status of CPU(s)

  ////////// Interface for SR instructions to write aux regs ///////////////
  //
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r,     // Aux write data

  input                       aux_timer_active, 


  input                       aux_tm0_ren_r,    // Aux region select for Read
  input      [1:0]            aux_tm0_raddr_r,  // Aux address for Read
  input                       aux_tm0_wen_r,    // Aux region select for Write
  input      [1:0]            aux_tm0_waddr_r,  // Aux address for Write

  output reg [`npuarc_DATA_RANGE]    tm0_aux_rdata,     // LR read data
  output reg                  tm0_aux_illegal,   // SR/LR operation is illegal
  output reg                  tm0_aux_k_rd,      // op needs Kernel R perm
  output reg                  tm0_aux_k_wr,      // op needs Kernel W perm
  output reg                  tm0_aux_unimpl,    // LR/SR reg is not present
  output reg                  tm0_aux_serial_sr, // SR should be serializing

  ////////// Interface to the IRQ unit /////////////////////////////////
  //
  //
  output reg [`npuarc_IRQM_RANGE]    timer0_irq_1h, // One-hot-encoded timer0 int
  input                       irq_clk_en_r,  // 2-cycle interrupt clk enable
  ////////// Watchdog reset output signals /////////////////////////////////
  //
  output  reg                 watchdog_reset  // Assert Watchdog reset
);

// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Signal/Register Declerations                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg [31:0]               aux_count0_nxt;
reg                      aux_count0_wen;
reg                      aux_count0_en;
reg [31:0]               aux_limit0_nxt;
reg                      aux_limit0_wen;
reg                      aux_limit0_en;
reg [4:0]                aux_control0_nxt;
reg                      aux_control0_wen;
reg                      aux_control0_en;

reg [31:0]               aux_count0_r;
reg [31:0]               aux_limit0_r;
reg [4:0]                aux_control0_r;

reg                      wd0_timeout_en;
reg                      wd0_timeout_r;

reg                      timer0_limit_reached;
reg                      timer0_count_incr;
reg                      timer0_disabled;

reg                      ip0_2cycle_r;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting aux register value for an LR           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : tm0_aux_lr_PROC
  tm0_aux_rdata      = `npuarc_DATA_SIZE'd0;
  tm0_aux_k_rd       = 1'b0;
  tm0_aux_k_wr       = 1'b0;
  tm0_aux_unimpl     = 1'b1;
  tm0_aux_illegal    = 1'b0;
  tm0_aux_serial_sr  = 1'b0;

  if (aux_tm0_ren_r == 1'b1)
  begin
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  case expression is `AUX_REG_BITS wide
//      cases selected are also `AUX_REG_BITS wide
//      Therefore there is no width mismatch
    case ({{(`npuarc_AUX_REG_BITS-2){1'b0}}, aux_tm0_raddr_r})
      (`npuarc_COUNT0_AUX & {{(`npuarc_AUX_REG_BITS-2){1'b0}}, 2'b11}):      // K_RW
      begin
        tm0_aux_rdata       = aux_count0_r;
        tm0_aux_k_rd        = 1'b1;
        tm0_aux_k_wr        = 1'b1;
        tm0_aux_unimpl      = 1'b0;
      end

      (`npuarc_LIMIT0_AUX & {{(`npuarc_AUX_REG_BITS-2){1'b0}}, 2'b11}):      // K_RW
      begin
        tm0_aux_rdata       = aux_limit0_r;
        tm0_aux_k_rd        = 1'b1;
        tm0_aux_k_wr        = 1'b1;
        tm0_aux_unimpl      = 1'b0;
      end

      (`npuarc_CONTROL0_AUX & {{(`npuarc_AUX_REG_BITS-2){1'b0}}, 2'b11}):    // K_RW
      begin
        tm0_aux_rdata[4:0]  = aux_control0_r;
        tm0_aux_k_rd        = 1'b1;
        tm0_aux_k_wr        = 1'b1;
        tm0_aux_unimpl      = 1'b0;
        tm0_aux_serial_sr   = 1'b1;
      end

      default:
      begin
        tm0_aux_unimpl      = 1'b1;
      end
    endcase
//spyglass enable_block W263
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting an SR                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : tm0_aux_wen_PROC
  aux_count0_wen       = 1'b0;
  aux_limit0_wen       = 1'b0;
  aux_control0_wen     = 1'b0;
  if (aux_tm0_wen_r == 1'b1)
//spyglass disable_block W263
// SMD: Reports case expression, select width mismatch
// SJ:  case expression is `AUX_REG_BITS wide
//      cases selected are also `AUX_REG_BITS wide
//      Therefore there is no width mismatch
    case ({{(`npuarc_AUX_REG_BITS-2){1'b0}}, aux_tm0_waddr_r})
      (`npuarc_COUNT0_AUX & {{(`npuarc_AUX_REG_BITS-2){1'b0}}, 2'b11}):    aux_count0_wen    = 1'b1;
      (`npuarc_LIMIT0_AUX & {{(`npuarc_AUX_REG_BITS-2){1'b0}}, 2'b11}):    aux_limit0_wen    = 1'b1;
      (`npuarc_CONTROL0_AUX & {{(`npuarc_AUX_REG_BITS-2){1'b0}}, 2'b11}):  aux_control0_wen  = 1'b1;
      default:  ;
    endcase
//spyglass enable_block W263
end

//////////////////////////////////////////////////////////////////////////////
//  Timers combinational logic
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : t0_count_PROC
  // Timer limit reached flag.
  //
  timer0_limit_reached = (aux_count0_r == aux_limit0_r);

  // Timer is disabled explictly by SW
  //
  timer0_disabled     = (aux_control0_r[`npuarc_TIMER_TD] == 1'b1);
  
  // Increment the timer only when the system debug unit is inactive
  // (debug instrutions take place instantaneously from the timers
  // perspective), and when the system is not halted.
  //
  timer0_count_incr =     (~timer0_disabled)
                         &&  (
                                  (    (aux_control0_r[`npuarc_TIMER_NH] == 1'b0))
                              ||  (    (sys_halt_r == 1'b0)
                                    && (db_active == 1'b0)
                                  )
                             )  
                             ;
end

//////////////////////////////////////////////////////////////////////////////
// aux_count next data and clock enable
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_count0_nxt_PROC
  aux_count0_nxt    = aux_count0_r;
  aux_count0_en     = 1'b0;

  if (aux_count0_wen)
  begin
    aux_count0_en   = 1'b1;
    aux_count0_nxt  = wa_sr_data_r;
  end
  else if (timer0_limit_reached)
  begin
    aux_count0_en   = 1'b1;
    aux_count0_nxt  = 32'd0;
  end
  else if (timer0_count_incr)
  begin
    aux_count0_en  = 1'b1;
    
    // leda W484 off
    // LMD: Possible loss of carry/borrow in add/sub
    // LJ:  Timer is wrap around counter
    //      Carry bit is redundant
    //      
    // leda BTTF_D002 off
    // LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
    // LJ:  Timer is wrap around counter
    //      Carry bit is redundant
    //      
    aux_count0_nxt = aux_count0_r + 1;
    // leda BTTF_D002 on
    // leda W484 on
  end
end

//////////////////////////////////////////////////////////////////////////////
// aux_limit next data and clock enable
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_limit0_nxt_PROC
  aux_limit0_nxt    = aux_limit0_r;
  aux_limit0_en     = 1'b0;

  if (aux_limit0_wen)
  begin
    aux_limit0_en  = 1'b1;
    aux_limit0_nxt = wa_sr_data_r;
  end
end

//////////////////////////////////////////////////////////////////////////////
// aux_control next data and clock enable
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_ctrl0_nxt_PROC
  aux_control0_nxt    = aux_control0_r;
  aux_control0_en     = 1'b0;

  if (aux_control0_wen)
  begin
    aux_control0_en   = 1'b1;
    aux_control0_nxt  =  wa_sr_data_r[4:0];
  end
  else if (timer0_limit_reached)
  begin
    aux_control0_en   = 1'b1;
    aux_control0_nxt  = {aux_control0_r[`npuarc_TIMER_TD],
                            aux_control0_r[`npuarc_TIMER_IE],
                            aux_control0_r[2:0]};
  end
end

//////////////////////////////////////////////////////////////////////////////
// Watchdog
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wd0_timouten_PROC
  wd0_timeout_en     =   timer0_limit_reached
                          & aux_control0_r[`npuarc_TIMER_W];
end // wd0_timouten_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Watchdog Reset Output
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : watchdog_PROC
   watchdog_reset    = 1'b0
                      | wd0_timeout_r
                      ;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronize IP bit to the IRQ unit's 2-cycle path                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : ip_sync_PROC
  if (rst_a == 1'b1)
    begin
    ip0_2cycle_r <= 1'b0;
    end
  else if (irq_clk_en_r == 1'b1)
    begin
    ip0_2cycle_r <= aux_control0_r[`npuarc_TIMER_IP];
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Outputs to the IRQ unit                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : timer_out_PROC
  // TIMER 0 interrupt vector
  //
  timer0_irq_1h        = `npuarc_IRQ_M'b0;
  timer0_irq_1h[16]     = ip0_2cycle_r;

end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining timer auxiliary registers                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : aux_count0_reg_PROC
  if (rst_a == 1'b1) begin
    aux_count0_r         <=  32'd0;
  end
  else if (aux_count0_en) begin
    aux_count0_r         <= aux_count0_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_limit0_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_limit0_r         <=  32'h00ffffff;
  end
  else if (aux_limit0_en) begin
    aux_limit0_r       <= aux_limit0_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : aux_control0_reg_PROC
  if (rst_a == 1'b1) begin
    aux_control0_r       <=  5'b00000;
  end
  else if (aux_control0_en) begin
    aux_control0_r       <= aux_control0_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : timeout0_PROC
  if (rst_a == 1'b1) begin
    wd0_timeout_r     <=  1'b0;
  end
  else if (wd0_timeout_en) begin
    wd0_timeout_r   <=  1'b1;
  end
end
// spyglass enable_block W193

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Output assignments   
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign timer_unit_enable = 1'b0
                         | aux_timer_active

                         | (aux_control0_r[`npuarc_TIMER_TD] == 1'b0)
                         ;
endmodule // alb_timers
