// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright 2010-2015 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2017, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------

// ===========================================================================
//
// Description:
//
//  This module implements the enhanced watchdog module for ARCv2EM  and
//  the ARCv2HS CPUs.
//  The Watchdog Timer Module is version 2.0 of the Watchdog Timer.        
//  This watchdog timer provides a window feature to monitor external      
//  events. This module also allows up to eight timers of various          
//  configurations.                                                        
//                                                                       
//  Refer to the programmer's reference manual to determine how to 
//  this timer                                                                 
// ==========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"
`include "const.def"


// spyglass disable_block STARC05-1.1.1.1
// SMD: File name does not match module name
// SJ:  Intentionally done, causes no issues
module npuarc_alb_watchdog (
// spyglass enable_block STARC05-1.1.1.1

  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,
  input                       clk2,
  input                       rst2_a,
  input                       rst_a,
  input                       irq_clk_en_r, // 2-cycle interrupt clk enable
  ////////// General input signals /////////////////////////////////////////
  //
  input                       db_active,     // Host debug op in progress

// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ:  halt not used in some config
  input                       sys_halt_r,    // halted status of CPU(s)
// spyglass enable_block W240

  ////////// Interface for SR instructions to write aux regs ///////////////
  //
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r,     // Aux write data

  input                       aux_read,         // Aux Read  Operation
  input                       aux_write,        // Aux Write Operation
  input                       aux_wdt_ren_r,    // Aux region select for Read
  input      [3:0]            aux_wdt_raddr_r,  // Aux address for Read
  input                       aux_wdt_wen_r,    // Aux region select for Write
  input      [3:0]            aux_wdt_waddr_r,  // Aux address for Write

  output reg [`npuarc_DATA_RANGE]    wdt_aux_rdata,     // LR read data
  output reg                  wdt_aux_illegal,   // SR/LR operation is illegal
  output reg                  wdt_aux_k_rd,      // op needs Kernel R perm
  output reg                  wdt_aux_k_wr,      // op needs Kernel W perm
  output reg                  wdt_aux_unimpl,    // LR/SR reg is not present
  output reg                  wdt_aux_serial_sr, // SR needs Serialization
  output reg                  wdt_aux_strict_sr, // SR must Serialize

  ////////// Interface to the IRQ unit /////////////////////////////////

  output reg [`npuarc_IRQM_RANGE]    wdt_int_timeout_1h_r,     // Interrupt timeout signal

  output reg                  wdt_unit_en_r,

  ////////// Watchdog external input/ output signals ///////////////////
  //
  // Generate External Inputs 
  output                      wdt_x3_stall,
  input                       x3_kill,

  
 //Generate acks the remaining watchdogs in configuration 2 if they exist
// spyglass disable_block W240
// SMD: unused input signal
// SJ:  part of wdt timeout interface
  input                       wdt_ext_timeout_ack_r,   // External timeout acknowledge
// spyglass enable_block W240
  output reg                  wdt_ext_timeout_r,       // External timeout signal    
  output reg                  wdt_reset2,              // Reset timeout signal from wdt clk
  output reg                  wdt_reset                // Reset timeout signal  
);



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Signal/Register Declerations                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                          aux_password_wen;
wire  [1:0]                  wdt_index_r;

reg                          wdt_en_lthresh_r;
reg                          wdt_en_uthresh_r;
reg                          wdt_en_control_r;
reg                          wdt_en_period_r;

reg                          aux_lthresh_wen;
reg                          aux_uthresh_wen;
reg                          aux_ctrl_wen;
reg                          aux_period_wen;


reg                          wd_timeout[`npuarc_WATCHDOG_NUM-1:0];

reg  [4-1:0]                  i_enable_regs_in;
wire [4-1:0]                  i_enable_regs_r;

// Generate the register/wires for the watchdog counters


//Watchdog timer 0

reg                          aux_ctrl0_wen;
reg                          aux_period0_wen;
reg   [31:0]                 wdt_period0_in;
wire  [31:0]                 wdt_period0_r;
reg   [31:0]                 wdt_period_cnt0_in;
wire  [31:0]                 wdt_period_cnt0_r;
wire  [`npuarc_WDT_CTRL_RANGE]      wdt_control0_r;
reg   [`npuarc_WDT_CTRL_RANGE]      wdt_control0_in;
reg                          wd_timeout0;

// This counter has additional threshold registers to support window function
//
reg   [31:0]                 wdt_lthresh0_in;
reg   [31:0]                 wdt_uthresh0_in;
wire  [31:0]                 wdt_lthresh0_r;
wire  [31:0]                 wdt_uthresh0_r;
reg                          aux_lthresh0_wen;
reg                          aux_uthresh0_wen;
reg                          wdt_win_err0_r;
reg                          wdt_win_good0_r;
reg                          wdt_ext_event0_r;
wire  [`npuarc_WATCHDOG_NUM-1:0]    wdt_control_p_err;
wire  [`npuarc_WATCHDOG_NUM-1:0]    wdt_period_cnt_p_err;
wire  [`npuarc_WATCHDOG_NUM-1:0]    wdt_period_p_err;
wire  [`npuarc_WATCHDOG_NUM-1:0]    wdt_lthresh_p_err;
wire  [`npuarc_WATCHDOG_NUM-1:0]    wdt_uthresh_p_err;
wire                         wdt_enb_regs_p_err;
wire                         wdt_passwd_sts_p_err;
  

reg                          wdt_ctrl0_wen_r;
reg                          wdt_period0_wen_r;
reg                          wdt_uthresh0_wen_r;
reg                          wdt_lthresh0_wen_r;
reg                          wdt_period0_cnt_syncd_r;
reg                          wdt_ctrl0_syncd_r;
reg                          wdt_period0_syncd_r;
reg                          wdt_uthresh0_syncd_r;
reg                          wdt_lthresh0_syncd_r;
// Sync signals for timer 0
wire                         sync_wr_period0_en;
wire                         sync_wr_period0_cnt_en;      
wire                         sync_wr_ctrl0_en;
wire                         sync_wr_lthresh0_en; 
wire                         sync_wr_uthresh0_en;
wire                         wdt_ext0_win_trig;
reg                          aux_lthresh0_ren;
reg                          aux_uthresh0_ren;
reg                          aux_ctrl0_ren;
reg                          aux_period0_cnt_ren;
reg                          aux_period0_ren;
reg                          wdt_int0_r;
reg                          wdt_int0_r_r;
reg                          wdt_ext0_timeout_vec_r;
reg                          wdt_reset0_vec_r;
reg                          wdt_int0_timeout_r;
reg                          wdt_ext0_timeout_r;
reg                          wdt_ext0_timeout_r_r;    
reg                          wdt_reset0_timeout_r;
reg                          wdt_reset0_timeout_r_r; 
reg                          aux_period0_cnt_wen;   
reg                          wdt_period0_cnt_wen_r;
wire                         wdt_set_timeout0_a;


reg                          wdt_reset_p1_r;   
reg                          wdt_ext_timeout_p1_r; 

reg [31:0]                   aux_rdata_r;
reg [31:0]                   aux_wdata_r;

reg                          wdt_read_d_r;
reg                          wdt_read_d_r_r;
reg                          wdt_read_done_r;  
reg                          wdt_read_done_r_r;   
reg                          wdt_read_r;
reg                          wdt_read_r_r;
reg                          wdt_read_busy_r; 
wire                         wdt_read_busy_tmp;
wire                         wdt_write_busy_tmp;
reg                          wdt_read_req_r; 
reg                          wdt_write_d_r;
reg                          wdt_write_d_r_r; 
reg                          wdt_write_r;

reg                          wdt_wen_r;
reg                          wdt_wen_r_r;   
reg                          wdt_write_done_r;
reg                          wdt_read_rdone_r;
reg                          wdt_write_wdone_r;


reg                          wdt_read_busy_r_r;
reg                          wdt_write_busy_r_r;

wire                         aux_read_ren;
wire                         aux_write_wen;

reg                          wdt_write_busy_r; 
reg                          wdt_write_req_r;
           
wire                         release_stall;
wire                         release_stall_wr;

wire                         wdt_parity_err;

wire                         i_sync_rd_ready_a;
wire                         i_sync_info_a;
reg [31:0]                   aux_wdata_syncd_r;
wire                         sync_wr_ready_a;
reg                          wdt_sync_ready_r;
reg                          wdt_sync_info_r;
wire                         wdt_sync_ready_a;
reg                          wdt_rw_syncd_r;


reg [31:0]                   aux_rdata_sync_r;
reg                          wdt_stall;

reg  [`npuarc_WATCHDOG_NUM-1:0]     wdt_flags_r;
reg  [`npuarc_WATCHDOG_NUM-1:0]     wdt_rst_timeout;
reg  [`npuarc_WATCHDOG_NUM-1:0]     wdt_set_timeout;
reg  [`npuarc_WATCHDOG_NUM-1:0]     wdt_set_timeout_r;

reg  [`npuarc_WATCHDOG_NUM-1:0]     wdt_rst_timeout_r;

reg  [`npuarc_WATCHDOG_NUM-1:0]     aux_set_rst_to;
reg  [`npuarc_WATCHDOG_NUM-1:0]     aux_set_rst_to_r;
reg  [`npuarc_WATCHDOG_NUM-1:0]     aux_set_rst_ext_to;
reg  [`npuarc_WATCHDOG_NUM-1:0]     aux_set_rst_ext_to_r;
reg  [`npuarc_WATCHDOG_NUM-1:0]     aux_set_rst_ext_ack_to;
reg  [`npuarc_WATCHDOG_NUM-1:0]     aux_set_rst_ext_ack_to_r;
wire                         wdt_parity_r;

wire  [`npuarc_WATCHDOG_NUM-1:0]    wdt_index_sel;

// This register is used to gather all the watchdog timeout signals      
reg                          wdt_int_r;

//Generate sync for additional ack signials 
 
reg                       wdt_ext_timeout_ack_1_r; // Timeout sync1
reg                       wdt_ext_timeout_ack_2_r; // Timeout sync2
wire                      wdt_ext_timeout_ack_s = wdt_ext_timeout_ack_2_r;

reg                          wdt_ext_event0_1_r;  //External Event Sync
reg                          wdt_ext_event0_p_r;  //External Event Sync
reg                          wdt_ext_event0_2_r;

reg [2:0]                    aux_state_r;
reg [2:0]                    aux_state_nxt;
reg                          aux_stall;
reg                          aux_wr_pending;
reg                          aux_wen_r;   
reg                          aux_wen_nxt;
reg                          aux_disable_r; 
reg                          aux_disable_nxt;
reg                          aux_wr_multi_cycle;
reg                          aux_multi_cycle;
reg                          aux_wr_pending_a;
reg                          aux_stall_a;
reg                          aux_multi_cycle_a;

reg                          ip_2cycle_r;


// spyglass disable_block AutomaticFuncTask-ML
// SMD: Function 'onehot' should be declared as automatic
// SJ: this function does not have any static var

function [`npuarc_WATCHDOG_NUM-1:0] onehot;
input [3:0]    index;
begin: onehot_func
reg   [`npuarc_WATCHDOG_NUM-1:0]  i_mask;
integer i;
             i_mask = `npuarc_WATCHDOG_NUM'b0;      
             for (i=0; i<`npuarc_WATCHDOG_NUM; i=i+1)
                  if (i==index) i_mask[i] = 1'b1;
             onehot = i_mask;
end
endfunction

// spyglass enable_block AutomaticFuncTask-ML



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// All the register instantiations are in this section                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

  
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// All the register instantiations are in this section                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
  

  
// Watchdog control register for timer 0  (may include parity checking)
//
npuarc_wd_parity #(6) u_wd_ctrl0(
                         .d_in (wdt_control0_in),
                         .clk  (clk2),
                         .rst  (rst2_a),
                         .watchdog_parity_err(wdt_control_p_err[0]),
                         .q_out (wdt_control0_r)
);


// Watchdog period counter register for timer 0  (may include parity checking)
//
npuarc_wd_parity #(32) u_wd_period_count0(
                         .d_in (wdt_period_cnt0_in),
                         .clk  (clk2),
                         .rst  (rst2_a),
                         .watchdog_parity_err(wdt_period_cnt_p_err[0]),
                         .q_out (wdt_period_cnt0_r)
);


// Watchdog period register for timer 0  (may include parity checking)
//
npuarc_wd_parity #(32) u_wd_period0(
                         .d_in (wdt_period0_in),
                         .clk  (clk2),
                         .rst  (rst2_a),
                         .watchdog_parity_err(wdt_period_p_err[0]),
                         .q_out (wdt_period0_r)
);


// Watchdog lower threshold register for timer 0  (may include parity checking)
//
npuarc_wd_parity #(32) u_wd_lthresh0(
                         .d_in (wdt_lthresh0_in),
                         .clk  (clk2),
                         .rst  (rst2_a),
                         .watchdog_parity_err(wdt_lthresh_p_err[0]),
                         .q_out (wdt_lthresh0_r)
);


// Watchdog upper threshold register for timer 0  (may includes parity checking)
//
npuarc_wd_parity #(32) u_wd_uthresh0(
                         .d_in (wdt_uthresh0_in),
                         .clk  (clk2),
                         .rst  (rst2_a),
                         .watchdog_parity_err(wdt_uthresh_p_err[0]),
                         .q_out (wdt_uthresh0_r)   
);


assign wdt_parity_err =     (|wdt_control_p_err) 
                          | (|wdt_period_cnt_p_err)
                                      | (|wdt_period_p_err)     
                          | (|wdt_lthresh_p_err)    
                          | (|wdt_uthresh_p_err)
                          ;
wire   core_reg_parity_err = 1'b0
                          | wdt_enb_regs_p_err
                          ;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Register Input Logic                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Timeout signal                                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

      if (wdt_control0_r[`npuarc_WDT_CTRL_WINEN]) 
          wd_timeout0 = (wdt_win_err0_r || 
                             (!wdt_win_good0_r && (wdt_period_cnt0_r == wdt_lthresh0_r))) &&
                              (wdt_control0_r[`npuarc_WDT_CTRL_ENB]) && !wdt_control0_r[`npuarc_WDT_CTRL_FLAG];
      else
          wd_timeout0 = (wdt_period_cnt0_r == 0) && !wdt_control0_r[`npuarc_WDT_CTRL_FLAG] &&
                              (wdt_control0_r[`npuarc_WDT_CTRL_ENB]);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Watchdog Module control register - wdt_en_control0_r[4:0]              //
//                                                                        //
//  Bit 0   - Enable                                                      //
//  Bit 1-2 - Trigger - Interrupt, External Signal, Reset                 //
//  Bit 3   - T - the timeout flag                                        //
//  Bit 4   - WIN_EN - enable for window function                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

  // Set default for control register
  //
  wdt_control0_in = wdt_control0_r;

  // Set the flag in the register if there is a counter timeout 
  //   
  if (wd_timeout0==1'b1)
      wdt_control0_in[`npuarc_WDT_CTRL_FLAG] = 1'b1;

  if (sync_wr_ctrl0_en)                
  begin
      wdt_control0_in = aux_wdata_syncd_r[`npuarc_WDT_CTRL_RANGE]; 
      wdt_control0_in[`npuarc_WDT_CTRL_FLAG] = (aux_wdata_syncd_r[`npuarc_WDT_CTRL_FLAG])?
                                              wdt_control0_r[`npuarc_WDT_CTRL_FLAG] :
                                              1'b0;
  end          

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Period Register                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

  // Set default value for period register
  //
  wdt_period0_in = wdt_period0_r;
  
  // This is normal write functional for the register
  //
  
  if (sync_wr_period0_en)   
    wdt_period0_in  = aux_wdata_syncd_r[`npuarc_WDT_CNT_RANGE0];  

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Counter Register                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Ac_conv01
// SMD: synchronizers converging on combinational gate
// SJ:  halt/debug considered here as expected
  // Set default for the counter register
  //
  wdt_period_cnt0_in = wdt_period_cnt0_r; 

  if (sync_wr_period0_en)
      wdt_period_cnt0_in = aux_wdata_syncd_r[`npuarc_WDT_CNT_RANGE0];        
              
  else if ((sync_wr_period0_cnt_en) &&
           wdt_control0_r[`npuarc_WDT_CTRL_WINEN]==1'b0 &&
           1'b1)
           wdt_period_cnt0_in = wdt_period0_r;        
                             
  else if (wdt_control0_r[`npuarc_WDT_CTRL_ENB]==1'b1 &&
           1'b1)
      begin
           if (wdt_control0_r[`npuarc_WDT_CTRL_WINEN]==1'b1)
               wdt_period_cnt0_in   = wdt_period_cnt0_r != 0 
              ?  wdt_period_cnt0_r - 1 : wdt_period0_r;  
           else
              wdt_period_cnt0_in   = wdt_period_cnt0_r - 1; 
      end
// spyglass enable_block Ac_conv01

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Threshold  Registers                                                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

  // Set default value for lower limit threshold register
  //
  
  wdt_lthresh0_in = wdt_lthresh0_r;
  
  if (sync_wr_lthresh0_en)       
    wdt_lthresh0_in  = aux_wdata_syncd_r[`npuarc_WDT_CNT_RANGE0];

  // Set default value for upper limit threshold register
  //
  wdt_uthresh0_in = wdt_uthresh0_r;
  
  if (sync_wr_uthresh0_en)         
    wdt_uthresh0_in  = aux_wdata_syncd_r[`npuarc_WDT_CNT_RANGE0];

    




end    



  

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Window                                                                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////




// Assert window event signal
//
assign wdt_ext0_win_trig = !wdt_ext_event0_r & wdt_ext_event0_2_r;
  
always @(posedge clk2 or posedge rst2_a)
begin : wdt0_ext_in_sync0_PROC

        if (rst2_a==1'b1)
        begin
            wdt_win_err0_r    <= 1'b0;
            wdt_win_good0_r   <= 1'b0;
            wdt_ext_event0_r  <= 1'b0;
        end
        else
        begin  
        
            wdt_ext_event0_r <= wdt_ext_event0_2_r;
            
            // Set the error flag for event outside window and second evend inside the window.
            //
            wdt_win_err0_r <= (((wdt_uthresh0_r < wdt_period_cnt0_r) && wdt_ext0_win_trig)  ||
                               ((wdt_lthresh0_r > wdt_period_cnt0_r) && wdt_ext0_win_trig)) ||
                                (wdt_win_good0_r && (wdt_lthresh0_r <= wdt_period_cnt0_r) && 
                                 wdt_ext0_win_trig)  ? 1'b1 : 1'b0;
  
            // Set good flag, when trigger is between the two threshold limits
            //
            if ((wdt_uthresh0_r >= wdt_period_cnt0_r) &&
                (wdt_lthresh0_r <= wdt_period_cnt0_r) && wdt_ext0_win_trig)
                 wdt_win_good0_r <= 1'b1; // Sets the good flag
                  
            else if ((wdt_period_cnt0_r >= wdt_uthresh0_r) ||
                    (sync_wr_period0_en))         
                     wdt_win_good0_r <= 1'b0; //Clears the flag

 
         end
           
end


 

// Always select index (timer) 0 in this configuration
//
assign wdt_index_r = 2'b0;
 
// Always select timer 0
//
assign wdt_index_sel = 1'b1;

  
  
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Password register enable signals                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

npuarc_wd_parity #(4) u_wd_enable_reg (
                  .d_in (i_enable_regs_in), 
                  .clk  (clk),
                  .rst  (rst_a),
                  .watchdog_parity_err(wdt_enb_regs_p_err),
                  .q_out (i_enable_regs_r)
);
  
always @*
begin : wdt_registers_PROC

    i_enable_regs_in = i_enable_regs_r;


    // Access the control register
    //
    if (i_enable_regs_r[1] == 1'b1 && aux_ctrl_wen == 1'b1)
    begin
        i_enable_regs_in[1] = 1'b0;        
    end
    else if (aux_password_wen == 1'b1 && wa_sr_data_r[7:0] == 8'hAA)
    begin
        i_enable_regs_in[1] = 1'b1;
    end

    // Access the period register
    // 
    if (i_enable_regs_r[0] == 1'b1 && aux_period_wen == 1'b1)
    begin
      i_enable_regs_in[0] = 1'b0;
    end
    else if (aux_password_wen == 1'b1 && wa_sr_data_r[7:0] == 8'h55)            
    begin
      i_enable_regs_in[0] = 1'b1;  
    end

    // Access the threshold lower register
    //
    if (i_enable_regs_r[2] == 1'b1 && aux_lthresh_wen == 1'b1)
    begin
      i_enable_regs_in[2] = 1'b0;
    end
    else if (aux_password_wen == 1'b1 && wa_sr_data_r[7:0] == 8'h56)            
    begin
      i_enable_regs_in[2] = 1'b1; 
    end

    // Access the threshold upper register
    //
    if (i_enable_regs_r[3] == 1'b1 && aux_uthresh_wen == 1'b1)
    begin
      i_enable_regs_in[3] = 1'b0;
    end
    else if (aux_password_wen == 1'b1 && wa_sr_data_r[7:0] == 8'h57)            
    begin
      i_enable_regs_in[3] = 1'b1;   
    end

end

always @*
begin : wdt_regs_assign_PROC

      wdt_en_period_r  = i_enable_regs_r[0];
      wdt_en_control_r = i_enable_regs_r[1];
      wdt_en_lthresh_r = i_enable_regs_r[2];
      wdt_en_uthresh_r = i_enable_regs_r[3];
            
end

// Signal to indicate that the watchdog unit is active. Bit 0 in cotrol
// register of each watchdog timer indicates whether it is active or not. OR
// the enable signals of all counters to generate watchdog unit enable.
wire wdt_unit_en_nxt;

assign wdt_unit_en_nxt = (1'b0
          | (aux_ctrl0_wen)
                              ) ? wa_sr_data_r[`npuarc_WDT_CTRL_ENB] : wdt_unit_en_r;

always @( posedge clk or posedge rst_a )
begin : wdt_unit_en_PROC
   if( rst_a )          wdt_unit_en_r <= 1'b0;
   else                 wdt_unit_en_r <= wdt_unit_en_nxt;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @aux_PROC: Auxiliary register interface                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: aux_write_PROC

  // Write enable signals
  //
  aux_password_wen     = 1'b0;
  aux_ctrl_wen         = 1'b0;
  aux_period_wen       = 1'b0;
  aux_lthresh_wen      = 1'b0;
  aux_uthresh_wen      = 1'b0; 
  aux_ctrl0_wen        = 1'b0;
  aux_period0_wen      = 1'b0;
  aux_period0_cnt_wen  = 1'b0;
  aux_lthresh0_wen     = 1'b0;
  aux_uthresh0_wen     = 1'b0;
  aux_wr_multi_cycle   = 1'b0;
  wdt_rst_timeout      = `npuarc_WATCHDOG_NUM'b0;

 if (aux_wdt_wen_r)
  begin
  
////////////////////////////////////////////////////////////////////////////
//  Case statement for AUX Indirect Registers                             //
////////////////////////////////////////////////////////////////////////////

    case (aux_wdt_waddr_r)

   // Write to the WDT_PASSWORD register
   // 
   `npuarc_WDT_PASSWD_AUX:
    begin   
         aux_password_wen = 1'b1;
         aux_wr_multi_cycle = (wa_sr_data_r[7:0] == 8'h5A);
                
         aux_period0_cnt_wen = wdt_index_sel[0] & (wa_sr_data_r[7:0] == 8'h5A); // K_RW

    end
    
     
   // Write to the WDT_CTRL register
   //       
   `npuarc_WDT_CTRL_AUX:
    begin
          aux_ctrl_wen = 1'b1; 
          aux_wr_multi_cycle = 1'b1;  

          aux_ctrl0_wen = (wdt_en_control_r | db_active) & 
                                wdt_index_sel[0]; // K_RW

          if (aux_ctrl0_wen)
          begin
              wdt_rst_timeout[0]= !wa_sr_data_r[`npuarc_WDT_CTRL_FLAG];
          end   

    end
    
   // Write to the WDT_PERIOD register
   //       
   `npuarc_WDT_PERIOD_AUX:
    begin        
          aux_period_wen = 1'b1;  
          aux_wr_multi_cycle = 1'b1;                   

           aux_period0_wen  =  (wdt_en_period_r | db_active) &
                                       wdt_index_sel[0]; // K_RW
    end

   // Write to the WDT_LTHRESH register
   //        
   `npuarc_WDT_LTHRESH_AUX:
    begin  
      aux_lthresh_wen      = 1'b1;
      aux_wr_multi_cycle = 1'b1;                                                         

      aux_lthresh0_wen   = (wdt_en_lthresh_r | db_active) &
                                  wdt_index_sel[0]; // K_RW
      
    end

   // Write to the WDT_UTHRESH register
   //         
   `npuarc_WDT_UTHRESH_AUX:
    begin      
      aux_uthresh_wen      = 1'b1;
      aux_wr_multi_cycle = 1'b1;  

      aux_uthresh0_wen   = (wdt_en_uthresh_r | db_active) &
                                 wdt_index_sel[0]; // K_RW
    end

// spyglass disable_block W193   
     default:
            ;
    endcase 
// spyglass enable_block W193 
  end


end

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//  Auxiliary access phase.                                                   //
//                                                                            //
//  This process handles the start of an auxiliary read/write access in       //
//  stage X3. This is were we resolve the access permissions of the operation //
//  and provide data for LR read instructions.If there is a need to stall the //
//  the aux access in X3, wdt_stall is asserted high. This happens when an LR //
//  instruction must be stalled (due to a multi-cyle read access or a multi-  //
//  write access)                                                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

always @*
begin: aux_read_PROC
  // AUX bus output.
  //
  // spyglass disable_block Ac_conv01
  // SMD: synchronizers converging on combinational gate
  // SJ: the error inject end signal is sync'd using TMR, and the converge is due to TMR majority voting
  wdt_aux_rdata        = `npuarc_DATA_SIZE'h0;
  // spyglass enable_block Ac_conv01
  wdt_aux_k_rd         = 1'b0;
  wdt_aux_k_wr         = 1'b0;
  wdt_aux_illegal      = 1'b0;
  wdt_aux_serial_sr    = 1'b0;
  wdt_aux_unimpl       = 1'b1;  
  wdt_aux_strict_sr     = 1'b0;

  aux_lthresh0_ren     = 1'b0;
  aux_uthresh0_ren     = 1'b0;
  aux_period0_cnt_ren  = 1'b0;
  aux_ctrl0_ren        = 1'b0;
  aux_period0_ren      = 1'b0;
  wdt_stall            = 1'b0;
  aux_multi_cycle      = 1'b0;

if (aux_wdt_ren_r)
begin
        
     case (aux_wdt_raddr_r)

      // An illegal read from WDT_PASSWORD register
      // 
      `npuarc_WDT_PASSWD_AUX:
      begin            
             wdt_aux_k_wr      = 1'b1; 
             wdt_aux_strict_sr = 1'b1;
             wdt_aux_illegal   = aux_read;  
             wdt_aux_unimpl    = 1'b0;

             // Stall this access if there is a pending write or busy/inflight auxiliary operations
             // 
             wdt_stall = aux_stall_a & !db_active & !aux_read; 
             aux_multi_cycle = !aux_read & !db_active;

      end 
 
      // Read from WDT_PASSWD_STATUS register
      //
      `npuarc_WDT_PASSWD_STS_AUX:
       begin

          wdt_aux_illegal = aux_write;
          wdt_aux_k_wr    = 1'b1;  
          wdt_aux_k_rd    = 1'b1;
          wdt_aux_strict_sr = aux_write;          
          wdt_aux_unimpl   = 1'b0;
          wdt_aux_rdata    = {26'b0, 2'b0, i_enable_regs_r}; 
     end
     
     // Read from WDT_CTRL register
     //              
     `npuarc_WDT_CTRL_AUX:
      begin    
             // Stall this access if there is a pending write or busy/inflight auxiliary operations
             //
             wdt_stall = aux_stall_a;
             aux_multi_cycle = 1'b1;

             // Initial read request signal(s) from the clk domain.  
             //
             aux_ctrl0_ren     = wdt_index_sel[0] & aux_read & !aux_wr_pending_a & !(wdt_read_busy_r | wdt_write_busy_r);

            wdt_aux_illegal = ~wdt_en_control_r & aux_write;
            wdt_aux_k_wr    = 1'b1;  
            wdt_aux_k_rd    = 1'b1;
            wdt_aux_strict_sr = aux_write;          
            wdt_aux_unimpl   = 1'b0;
                                     
            case (wdt_index_r)
             0: wdt_aux_rdata = {aux_rdata_r[31:4], wdt_flags_r[0], aux_rdata_r[2:0]};
            default:
            begin
                  wdt_aux_unimpl  = 1'b1;                
                  wdt_stall = 1'b0;
            end
            endcase

      end   
      
   
     // Read/Write to the WDT_PERIOD register
     //                      
      `npuarc_WDT_PERIOD_AUX:
      begin
             // Stall this access if there is a pending write or busy/inflight auxiliary operations
             //
             wdt_stall = aux_stall_a; 
             aux_multi_cycle = 1'b1;

             // Initial read request signal(s) from the clk domain.  
             //
             aux_period0_ren  = wdt_index_sel[0] & aux_read & !aux_wr_pending_a & !(wdt_read_busy_r | wdt_write_busy_r);

             wdt_aux_k_wr      = 1'b1;
             wdt_aux_k_rd      = 1'b1;    
             wdt_aux_illegal   = ~wdt_en_period_r & aux_write;
             wdt_aux_strict_sr = aux_write;      
             wdt_aux_unimpl    = 1'b0;
            
             case (wdt_index_r)
             0: wdt_aux_rdata =  aux_rdata_r;
            default:
            begin
                  wdt_aux_unimpl  = 1'b1;                
                  wdt_stall = 1'b0;
            end
            endcase

      end
             
     // Read from WDT_COUNT register
     //              
      `npuarc_WDT_COUNT_AUX:
      begin

             // Stall this access if there is a pending write or busy/inflight auxiliary operations
             //
             wdt_stall = aux_stall_a; 
             
             aux_multi_cycle = 1'b1;
             
             // Initial read request signal(s) from the clk domain.  
             //
             aux_period0_cnt_ren  = wdt_index_sel[0] & aux_read & !aux_wr_pending_a & !(wdt_read_busy_r | wdt_write_busy_r);
             wdt_aux_k_rd    = 1'b1;
             wdt_aux_illegal = aux_write; 
             wdt_aux_unimpl   = 1'b0;
           
             case (wdt_index_r)
             0: wdt_aux_rdata =  aux_rdata_r;
             default:
             begin
                   wdt_aux_unimpl  = 1'b1;               
                  wdt_stall = 1'b0;
             end
             endcase
      end  
                     
     // Read/Write to the WDT_LTHRESH register
     //  
      `npuarc_WDT_LTHRESH_AUX:
      begin
             // Stall this access if there is a pending write or busy/inflight auxiliary operations
             //                
             wdt_stall = aux_stall_a & (
                     wdt_index_sel[0] |
                           1'b0);
                            
             aux_multi_cycle = 
                              (wdt_index_sel[0] & ((wdt_en_lthresh_r & aux_write) | aux_read)) |
                               1'b0;

             aux_lthresh0_ren  = wdt_index_sel[0] & aux_read & !aux_wr_pending_a & !(wdt_read_busy_r | wdt_write_busy_r);

             wdt_aux_k_wr = 1'b1;
             wdt_aux_k_rd = 1'b1;           
             wdt_aux_strict_sr = aux_write;         
             wdt_aux_unimpl   = 1'b0;
                     
             wdt_aux_illegal = (~wdt_en_lthresh_r |
                                 1'b0) & aux_write;

              case (wdt_index_r)
              0: wdt_aux_rdata =  aux_rdata_r;
              default:
              begin
                  wdt_aux_unimpl  = 1'b1;            
                  wdt_stall = 1'b0;
              end
              endcase
      end 
      
     // Read from WDT_UTHRESH register
     //               
      `npuarc_WDT_UTHRESH_AUX:
      begin
      
             // Stall this access if there is a pending write or busy/inflight auxiliary operations
             //                
             wdt_stall = aux_stall_a & (
                     wdt_index_sel[0] |
                           1'b0);
             
             aux_multi_cycle =
                              (wdt_index_sel[0] & ((wdt_en_uthresh_r & aux_write) | aux_read)) |
                               1'b0;

             aux_uthresh0_ren  = wdt_index_sel[0] & aux_read & !aux_wr_pending_a & !(wdt_read_busy_r | wdt_write_busy_r);

             wdt_aux_k_wr = 1'b1;
             wdt_aux_k_rd = 1'b1;
             wdt_aux_strict_sr = aux_write;           
             wdt_aux_unimpl   = 1'b0;
             
             wdt_aux_illegal =  (~wdt_en_uthresh_r |
                                 1'b0) & aux_write;
  
             case (wdt_index_r)
             0: wdt_aux_rdata =  aux_rdata_r;
             default:
             begin
                      wdt_aux_unimpl  = 1'b1;            
                  wdt_stall = 1'b0;
             end
             endcase
 
      end

        
      default:
      begin
             // aux_addr is not implemented in this module
             //
             wdt_aux_unimpl  = 1'b1;
      end
      endcase //Read Decode End
      

   end

end



always @(posedge clk or posedge rst_a)
begin : aux_state_PROC

      if (rst_a)
      begin
          aux_state_r   <= `npuarc_AUX_IDLE;
          aux_wen_r     <= 1'b0;
          aux_disable_r <= 1'b0;
      end
      else
      begin
          aux_state_r   <= aux_state_nxt;
          aux_wen_r     <= aux_wen_nxt;
          aux_disable_r <= aux_disable_nxt;       
      end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Stall control for multi-cycle LR/SR accesses                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: aux_intermediate_PROC

     aux_wr_pending_a  =  aux_wr_pending;
     aux_stall_a       =  aux_stall;
     aux_multi_cycle_a = aux_multi_cycle;
     
end
     
always @*
begin: Aux_stall_ctrl_PROC

      // AUX bus output.
      //
     aux_state_nxt   =  aux_state_r;
     aux_wr_pending  =  1'b0;
     aux_stall       =  1'b0;
     aux_wen_nxt     =  aux_wen_r;
     aux_disable_nxt =  aux_disable_r;

     case (aux_state_r)
     `npuarc_AUX_IDLE:
     begin     
           // Wait until we see an aux access that won't be killed (x3_kill-=0)  
   
           aux_stall = !(aux_wdt_ren_r & aux_write) & !aux_disable_r;    // stall for read ops

           if (aux_wdt_ren_r & aux_write & aux_multi_cycle_a & !x3_kill & !aux_disable_r)             
           begin
               aux_wen_nxt   = 1'b1;
               aux_state_nxt = `npuarc_AUX_WR_READY;           // wait for write op
           end    
           else if (aux_wdt_ren_r & aux_multi_cycle_a &
                    aux_read & !x3_kill & !aux_disable_r)
                begin
                    aux_wen_nxt   = 1'b0;
                    aux_state_nxt = `npuarc_AUX_BUSY;          // already started read op      
                end
               
           aux_disable_nxt = 1'b0;      
     end  
    
     `npuarc_AUX_WR_READY: 
     begin
     
           // Here we wait for a write op to be launched. If it is never launched
           // i.e. x3_kill = 1 we go back to the IDLE state. This means it was killed
           
           // never stall pipleine when writing to PASSWORD, INDEX or ECR registers. These
           // not multi-cycle write to the clk2 domain

           aux_wr_pending = 1'b1;
                      
           aux_stall = !(aux_wdt_wen_r & !aux_multi_cycle_a);
           
           if (aux_wdt_wen_r | x3_kill)
           begin 

               if (aux_wr_multi_cycle & !x3_kill)
                   aux_state_nxt = `npuarc_AUX_BUSY;
               else
                   aux_state_nxt = `npuarc_AUX_IDLE;
           end
                
     end     

     `npuarc_AUX_BUSY:
     begin
          // Currently in the middle of a multi-cycle LR/SR operations
          
          aux_stall = 1'b1;  // always a default stall
             
          if ( ((~wdt_read_busy_tmp) & (~wdt_write_busy_tmp)) | (release_stall_wr) )
              aux_state_nxt  = `npuarc_AUX_IDLE;
        
          if (!aux_wen_r)
          begin
              if  (release_stall)
              begin
                   aux_disable_nxt = 1'b1;
                   aux_state_nxt   = `npuarc_AUX_IDLE;
              end
              else if (x3_kill)
                    aux_state_nxt  = `npuarc_AUX_KILL;
          end   
                 
     end   
       
     `npuarc_AUX_KILL:  
     begin
         // continuely stall the pipeline until the outstanding LR/SR 
         // completes
         
         aux_stall = 1'b1;
         if ( ((~wdt_read_busy_tmp) & (~wdt_write_busy_tmp)) | (release_stall) )
             aux_state_nxt = `npuarc_AUX_IDLE;
    
     end
// spyglass disable_block W193      
     default:;
    endcase   
// spyglass enable_block W193 
    
end


always @(posedge clk or posedge rst_a)
begin : sync_set_ecr_r_PROC

      if (rst_a)
          wdt_set_timeout_r <= 0;
      else
          wdt_set_timeout_r <= wdt_set_timeout;
end

assign wdt_set_timeout0_a = !wdt_set_timeout_r[0] & wdt_set_timeout[0];


// spyglass disable_block Ac_conv02
// SMD: synchronizers converge on combinational gate
// SJ:  sycchronizer paths are from same domain, causes no issues
always @*
begin : sync_set_ecr_PROC

          wdt_set_timeout = 0;
          
          wdt_set_timeout[0] =  wdt_reset0_timeout_r_r |
                                  wdt_ext0_timeout_r_r   |
                                  wdt_int0_r_r;
                                  
end
// spyglass enable_block Ac_conv02


////////////////////////////////////////////////////////////////////////////////////
//                                                                                //
// Here we generate the read/write request and busy signals. The requests signals //
// are sync'd over to the clk2 domain to initiate a read/write with the target    //
// register.                                                                      //
//                                                                                //
//        req_clk (high) > flop > flop > req_clk2 (high)                          //
//                                                                                //
// When the request is seen in the clk2 domain we assert wdt_sync_ready_a to      //
// complete the read/write operation. When completed a done signal is sent back   //
// to the clk domain to deassert the original request signal. This done signal    //
// remains high until the req is deasserted low.                                  //
//                                                                                //
//        done_clk (high) < flop < flop < done_clk2 (high)                        //
//                                                                                //
// When the done signal is seen in clk domain, the request is desasserted. When   //
// the req signal is deasserted. The low signal goes back to the clk2 domain.     //
//                                                                                //
//        req_clk (low) > flop > flop > req_clk2 (low)                            //
//                                                                                //
// When a low is seen in the clk2 domain, the done signal is deasserted low in    //
// response to complete the access. Only when the done signal in the clk domain   //
// is deasserted is the operation considered completed.                           //
//                                                                                //
// A busy signal is driven to track the entire duration of this operation.        //
///                                                                               //
////////////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Ac_conv01
// SMD: synchronizers converging on combinational gate
// SJ:  signals functionally independent
// spyglass disable_block Ac_coherency06 
// SMD: Reports signals synchronized more than once in the same clock domain
// SJ: TMR logic will sync the input three times
always @(posedge clk or posedge rst_a)
begin : sync_busy_req_signals_PROC

       if (rst_a)
       begin
           wdt_write_busy_r   <= 1'b0; 
           wdt_read_busy_r    <= 1'b0;
           wdt_write_req_r    <= 1'b0;     
           wdt_read_req_r     <= 1'b0; 
           wdt_read_busy_r_r  <= 1'b0;
           wdt_write_busy_r_r <= 1'b0;
       end
       else
       begin


// Write data bus
//
           if (aux_write_wen)                 // set write request
               wdt_write_req_r  <= 1'b1; 
           else if (wdt_write_d_r_r)          // deassert when write done in clk2 domain 
                    wdt_write_req_r  <= 1'b0; // sync'd back to clk domain

           if (aux_write_wen)                 // set busy for the write operation
               wdt_write_busy_r  <= 1'b1; 
           else if (~wdt_write_d_r_r & wdt_write_wdone_r) // clear busy when failing edge write done
                wdt_write_busy_r  <= 1'b0;               

           wdt_write_busy_r_r  <= wdt_write_busy_r; // register for pulse generation (release stall)
                
// Read data bus
//              
           if (aux_read_ren & !x3_kill) // set read request
               wdt_read_req_r  <= 1'b1; 
           else if (wdt_read_d_r_r)            // deassert when read done in clk2 domain
                    wdt_read_req_r  <= 1'b0;   // sync'd back to clk domain
                
           if (aux_read_ren & !x3_kill) // set busy for the read operation
               wdt_read_busy_r  <= 1'b1; 
           else if (~wdt_read_d_r_r & wdt_read_rdone_r) // clear busy when failing edge read done
                    wdt_read_busy_r  <= 1'b0;
                        
           wdt_read_busy_r_r  <= wdt_read_busy_r; // register for pulse generation (release stall)

       end

end
// spyglass enable_block Ac_conv01
// spyglass enable_block Ac_coherency06 

always @(posedge clk or posedge rst_a)
begin : wdt_flag_clk_PROC

      if (rst_a)
         wdt_flags_r <= 0;
      else       
      begin
      // local flag bits for the EWDT_CTRL registers

          if (wdt_set_timeout0_a)  // For Timer 0
              wdt_flags_r[0] <= 1'b1;
          else if (wdt_rst_timeout[0])
                   wdt_flags_r[0] <= 1'b0;
          
      
      end

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sync request signals to the clk2 domain                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block Reset_sync04
// SMD:  Asynchronous reset signal synchronized at least twice
// SJ: These are not the reset synchronizers. Tool is not understanding them correctly, can be ignored.

// Sync signals to the CLK2 domains
//
always @(posedge clk2 or posedge rst2_a)
begin : sync_to_clk2_PROC

      if (rst2_a)
      begin
          wdt_wen_r            <= 1'b0;
          wdt_wen_r_r          <= 1'b0;   
          wdt_write_done_r     <= 1'b0;                     
          wdt_read_r           <= 1'b0;
          wdt_read_r_r         <= 1'b0;
          wdt_read_done_r      <= 1'b0;
          wdt_read_done_r_r    <= 1'b0;
      end
      else
      begin

          wdt_read_r        <= wdt_read_req_r;
          wdt_read_r_r      <= wdt_read_r;      // read req in clk2 domain
          wdt_read_done_r_r <= wdt_read_done_r; 
                                  
          if (i_sync_rd_ready_a)           // read data captured (now wait for orig req low)
              wdt_read_done_r <= 1'b1;
          else if (~wdt_read_r_r)          // wait for orig req deasserted to go low
                   wdt_read_done_r <= 1'b0; 

          wdt_wen_r        <= wdt_write_req_r;
          wdt_wen_r_r      <= wdt_wen_r;        // write req in clk2 domain        
  
          if (sync_wr_ready_a)           // data written to register (now wait for orig req low)
              wdt_write_done_r <= 1'b1;
          else if (~wdt_wen_r_r)               // wait for orig req deasserted to go low
                   wdt_write_done_r <= 1'b0; 
                   
      end

end
// spyglass enable_block Reset_sync04


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sync done signals to the clk domain                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : sync_control_clk_to_from_clk2_PROC

      if (rst_a)
      begin    
          wdt_write_d_r       <= 1'b0;
          wdt_write_d_r_r     <= 1'b0;
          wdt_write_wdone_r   <= 1'b0;
        
          wdt_read_d_r        <= 1'b0;
          wdt_read_d_r_r      <= 1'b0;
          wdt_read_rdone_r    <= 1'b0;       
      end
      else
      begin
      
          wdt_write_d_r     <= wdt_write_done_r;  // sync stage 1 - write completed
          wdt_write_d_r_r   <= wdt_write_d_r;     // sync stage 2
          wdt_write_wdone_r <= wdt_write_d_r_r;   // pulse signal                   
                    
          wdt_read_d_r      <= wdt_read_done_r;   // sync stage 1 - read completed
          wdt_read_d_r_r    <= wdt_read_d_r;      // sync stage 2
          wdt_read_rdone_r  <= wdt_read_d_r_r;    // pulse signal
      end


end



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Start a synchronized read/write operation                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign aux_read_ren = (
                      aux_period0_cnt_ren |    
                      aux_period0_ren |  
                      aux_ctrl0_ren |   
                      aux_lthresh0_ren |    
                      aux_uthresh0_ren |   
                      1'b0)
                      & !aux_disable_r
                      & !release_stall
                      & !wdt_write_busy_r             
                      & !wdt_read_busy_r
                      ;
                   

assign aux_write_wen = (
                      aux_period0_wen     |  
                      aux_period0_cnt_wen | 
                      aux_ctrl0_wen       |
                      aux_lthresh0_wen    | 
                      aux_uthresh0_wen    | 
                      1'b0) &
                      !wdt_write_busy_r;



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// register information from clk for use in clk2 domain                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : sync_write_data_PROC

      if (rst_a)
      begin
          aux_wdata_r           <= 0;
          wdt_period0_wen_r     <= 1'b0;
          wdt_ctrl0_wen_r       <= 1'b0;
          wdt_uthresh0_wen_r    <= 1'b0;
          wdt_lthresh0_wen_r    <= 1'b0;
          wdt_period0_cnt_wen_r <= 1'b0;
      end
      else
      begin

         if (aux_write_wen)
         begin
          aux_wdata_r           <= wa_sr_data_r; 
          
          wdt_period0_wen_r     <= aux_period0_wen;
          wdt_ctrl0_wen_r       <= aux_ctrl0_wen;
          wdt_uthresh0_wen_r    <= aux_uthresh0_wen;
          wdt_lthresh0_wen_r    <= aux_lthresh0_wen;
          wdt_period0_cnt_wen_r <= aux_period0_cnt_wen;
         end 
         else if (aux_read_ren)
         begin

          wdt_period0_wen_r     <= aux_period0_ren;
          wdt_ctrl0_wen_r       <= aux_ctrl0_ren;
          wdt_uthresh0_wen_r    <= aux_uthresh0_ren;
          wdt_lthresh0_wen_r    <= aux_lthresh0_ren;
          wdt_period0_cnt_wen_r <= aux_period0_cnt_ren;
                 
         end        
             
      end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Registering read data from the clk2 domain for sampling in the processor //
// clk domain                                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Ac_unsync02
// SMD: unsynchronized clock domain crossings for vector signals
// SJ:  qualifier is not recognized by the tool, these can be ignored.
always @(posedge clk2 or posedge rst2_a)
begin : read_EWDT_register_in_clk2_PROC

      if (rst2_a)
      begin
          aux_rdata_sync_r <= 32'b0;
      end
      else
      begin
         if (i_sync_rd_ready_a)
         begin

             if (wdt_period0_cnt_syncd_r)
                 aux_rdata_sync_r <= wdt_period_cnt0_r; 
             
             else if (wdt_period0_syncd_r)
                 aux_rdata_sync_r <= wdt_period0_r; 
             
             else if (wdt_ctrl0_syncd_r)
                 aux_rdata_sync_r <= wdt_control0_r; 
             
             else if (wdt_lthresh0_syncd_r)
                 aux_rdata_sync_r <= wdt_lthresh0_r; 

             else if (wdt_uthresh0_syncd_r)
                 aux_rdata_sync_r <= wdt_uthresh0_r; 

                 
       end     
      end
end
// spyglass enable_block Ac_unsync02

                              
// spyglass disable_block Ac_unsync02
// SMD: unsynchronized clock domain crossings for vector signals
// SJ:  qualifier is not recognized due to DCLS delays the qualifier and rules set cdc_qualifier_depth to 0
always @(posedge clk or posedge rst_a)
begin : sync_data_flow_PROC

     if (rst_a)
         aux_rdata_r <= 0;
     else 
         aux_rdata_r <= wdt_read_rdone_r ? aux_rdata_sync_r : aux_rdata_r;  
 
end
// spyglass enable_block Ac_unsync02

// Release the stall of LR instruction in the commit statge (falling edge detect)
//
assign release_stall = !wdt_read_busy_r & wdt_read_busy_r_r;
assign wdt_read_busy_tmp = wdt_read_busy_r | wdt_read_busy_r_r;

assign release_stall_wr = !wdt_write_busy_r & wdt_write_busy_r_r;
assign wdt_write_busy_tmp = wdt_write_busy_r | wdt_write_busy_r_r;




// Sync update signals for timer 0
assign sync_wr_period0_en = wdt_period0_syncd_r &  sync_wr_ready_a;
assign sync_wr_period0_cnt_en = wdt_period0_cnt_syncd_r &  sync_wr_ready_a; 
assign sync_wr_ctrl0_en = wdt_ctrl0_syncd_r &  sync_wr_ready_a;
assign sync_wr_lthresh0_en = wdt_lthresh0_syncd_r &  sync_wr_ready_a;       
assign sync_wr_uthresh0_en = wdt_uthresh0_syncd_r &  sync_wr_ready_a;


// spyglass disable_block Ac_conv02
// SMD: synchronizers converge on combinational gate
// SJ:  sycchronizer paths are from same domain, causes no issues
// Synchronize information enable signal
// 
assign i_sync_info_a  = wdt_wen_r_r | wdt_read_r_r;
// spyglass enable_block Ac_conv02

// Syync the write ready
//                   
assign sync_wr_ready_a = wdt_rw_syncd_r & wdt_sync_ready_r;


// Syync the read ready
//
assign i_sync_rd_ready_a = !wdt_rw_syncd_r & wdt_sync_ready_r; 
                       

// Generate a pulse to capture the information for clk 2 domain
//
assign wdt_sync_ready_a = !wdt_sync_info_r & i_sync_info_a;


// spyglass disable_block Ac_unsync01
// spyglass disable_block Ac_unsync02
// SMD: unsynchronized clock domain crossings for vector signals
// SJ:  qualifier is not recognized due to DCLS delays the qualifier and rules set cdc_qualifier_depth to 0
always @(posedge clk2 or posedge rst2_a)
begin : sync_write_data_clk2_PROC

      if (rst2_a)
      begin
          aux_wdata_syncd_r       <= 32'b0;
          wdt_period0_syncd_r     <= 1'b0;
          wdt_ctrl0_syncd_r       <= 1'b0;
          wdt_uthresh0_syncd_r    <= 1'b0;
          wdt_lthresh0_syncd_r    <= 1'b0;
          wdt_period0_cnt_syncd_r <= 1'b0;
          wdt_sync_ready_r         <= 1'b0;       
          wdt_sync_info_r          <= 1'b0;
          wdt_rw_syncd_r           <= 1'b0;
      end
      else
      begin
          wdt_sync_info_r            <= i_sync_info_a;         
          wdt_sync_ready_r           <=  wdt_sync_info_r;
          aux_wdata_syncd_r          <= (wdt_sync_ready_a)? aux_wdata_r : aux_wdata_syncd_r;                    
          wdt_rw_syncd_r             <= (wdt_sync_ready_a)? wdt_write_busy_r : wdt_rw_syncd_r;
          wdt_period0_syncd_r        <= (wdt_sync_ready_a)? wdt_period0_wen_r : wdt_period0_syncd_r;
          wdt_ctrl0_syncd_r          <= (wdt_sync_ready_a)? wdt_ctrl0_wen_r : wdt_ctrl0_syncd_r;
          wdt_uthresh0_syncd_r       <= (wdt_sync_ready_a)? wdt_uthresh0_wen_r : wdt_uthresh0_syncd_r;
          wdt_lthresh0_syncd_r       <= (wdt_sync_ready_a)? wdt_lthresh0_wen_r : wdt_lthresh0_syncd_r;
          wdt_period0_cnt_syncd_r    <= (wdt_sync_ready_a)? wdt_period0_cnt_wen_r : wdt_period0_cnt_syncd_r;
             
      end
end
// spyglass enable_block Ac_unsync01
// spyglass enable_block Ac_unsync02



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Outputs to the IRQ unit                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : ip_sync_PROC
  if (rst_a == 1'b1)
      begin
        ip_2cycle_r <= 1'b0;
      end
      else if (irq_clk_en_r == 1'b1)
      begin
               ip_2cycle_r <= wdt_int_r; 
      end
end

always @*
begin : timer_int_out_PROC

  // Watchdog interrupt vector
  //

  wdt_int_timeout_1h_r        = `npuarc_IRQ_M'b0;
  
  wdt_int_timeout_1h_r[18] =  ip_2cycle_r; 
   
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sync the ackowledgement and input signal                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Reset_sync04
// SMD:  Asynchronous reset signal synchronized at least twice
// SJ: These are not the reset synchronizers. Tool is not understanding them correctly, can be ignored.
always @(posedge clk2 or posedge rst2_a)
begin : sync_PROC
  if (rst2_a==1'b1)
  begin
  //Generate sync for additional ack signials

   wdt_ext_timeout_ack_1_r  <= 1'b0; 
   wdt_ext_timeout_ack_2_r  <= 1'b0;
   
    wdt_ext_event0_1_r  <= 1'b0;  //External Event Sync
    wdt_ext_event0_p_r  <= 1'b0; 
    wdt_ext_event0_2_r  <= 1'b0;  

  end
  else
  begin

    // Generate sync for additional ack signials in configuration 2
    wdt_ext_timeout_ack_1_r <= wdt_ext_timeout_ack_r;
    wdt_ext_timeout_ack_2_r <= wdt_ext_timeout_ack_1_r;

   
    // Software/external reset for timer 0
     if (sync_wr_period0_cnt_en && (aux_wdata_syncd_r[7:0]== 8'h5A) &&
        (wdt_control0_r[5:4]==2'b11)) 
    
        wdt_ext_event0_1_r  <= 1'b1;  //Windown event
     else  
        wdt_ext_event0_1_r <= 1'b0;  
    
     wdt_ext_event0_2_r <= wdt_ext_event0_1_r; 
 
  end
  
end
// spyglass enable_block Reset_sync04

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Holds the timeout signals for the watchdog module                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block Ac_conv01
// SMD: synchronizers converging on combinational gate
// SJ:  signals functionally independent


always @(posedge clk2 or posedge rst2_a)
begin : timeout0_PROC

  if (rst2_a==1'b1)
  begin
    wdt_ext0_timeout_vec_r <= 1'b0;
    wdt_reset0_vec_r       <=  1'b0;
    wdt_int0_timeout_r     <=  1'b0;    
  end
  else
  begin
  
    //
    // Signal via an external signal that a timeout has occurred. 
    //
    if (sync_wr_ctrl0_en)
    begin
        wdt_ext0_timeout_vec_r <= (aux_wdata_syncd_r[`npuarc_WDT_CTRL_FLAG])? wdt_ext0_timeout_vec_r : 1'b0;
        wdt_reset0_vec_r       <= (aux_wdata_syncd_r[`npuarc_WDT_CTRL_FLAG])? wdt_reset0_vec_r: 1'b0;    
        wdt_int0_timeout_r     <= (aux_wdata_syncd_r[`npuarc_WDT_CTRL_FLAG])? wdt_int0_timeout_r: 1'b0;
    end                     
    else
    begin

        if ((wdt_ext_timeout_ack_s==1'b1) && (wdt_control0_r[`npuarc_WDT_CTRL_TRIG]==2'b00))         
            wdt_ext0_timeout_vec_r <=  1'b0; 

                                
        else if ((wd_timeout0==1'b1) && !(^wdt_control0_r[`npuarc_WDT_CTRL_TRIG]))
                 wdt_ext0_timeout_vec_r <=  1'b1; 
 
        // Assert a level interrupt
        if ((wd_timeout0==1'b1) && (wdt_control0_r[`npuarc_WDT_CTRL_TRIG]==2'b01)) //Set
            wdt_int0_timeout_r  <=  1'b1;  
   
        // Initiate a system reset
        if ((wd_timeout0==1'b1) && (wdt_control0_r[`npuarc_WDT_CTRL_TRIG]==2'b10)) //Set
             wdt_reset0_vec_r  <=  1'b1;

    end

  end
  
end
        
     
// spyglass enable_block Ac_conv01 
 


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Sync the interrupt signals from clk2 domain to the clk domain           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// spyglass disable_block Ac_conv02
// SMD: same-domain signals that are synchronized in the same destination domain and converge before sequential elements.
// SJ:  each wdt timers are considered independent and the timeout irq can be converged at core clock domain
// spyglass disable_block Ac_conv01
// SMD: signals from the same domain that are synchronized in the same destination domain and converge after any number of sequential elements
// SJ:  each wdt timers are considered independent and the timeout irq can be converged at core clock domain
always @(posedge clk or posedge rst_a)  
begin
  if (rst_a==1'b1)
  begin : wdt_int_sync_PROC
    wdt_int_r          <= 1'b0;
    wdt_int0_r   <= 1'b0;
    wdt_int0_r_r <= 1'b0;
  end
  else
  begin
       wdt_int0_r <= wdt_int0_timeout_r;  // sync interrupt signal for timer 0
       wdt_int0_r_r <= wdt_int0_r;
  
       wdt_int_r <=                                   // final output for interrupt
                     wdt_int0_r_r |  
                    1'b0;
  
  end
  
end
// spyglass enable_block Ac_conv02
// spyglass enable_block Ac_conv01



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Parity error signal for timer registers                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg parity_err_r;
reg parity_wait_clr_r;
                
always @(posedge clk or posedge rst_a)  
begin
      if (rst_a==1'b1)
      begin
          parity_err_r <= 1'b0;
          parity_wait_clr_r <= 1'b0;
      end
      else
      begin

          if (parity_wait_clr_r)
          begin
              if (wdt_parity_r==0)
                   parity_wait_clr_r <= 1'b0;
          end   
          else if (wdt_parity_r)
                   parity_err_r <= 1'b1;
          else
          begin
                   parity_wait_clr_r <= parity_wait_clr_r;
                   parity_err_r <= parity_err_r;
          end
      end
end     
// spyglass disable_block Ac_conv02
// SMD: Reports same-domain signals that are synchronized in the same destination domain and converge before sequential elements.
// SJ:  each wdt timers are considered independent and the timeout irq can be converged at core clock domain

  npuarc_cdc_sync wdt_parity_r_sync (
                              .clk   (clk),
                              .rst_a (rst_a),
                              .din   (wdt_parity_err),
                              .dout  (wdt_parity_r)
                             );


always @(posedge clk2 or posedge rst2_a)
begin : wdt_parity_err_r_PROC
  if (rst2_a==1'b1)
  begin
    wdt_reset2          <= 1'b0;
  end
  else
  begin
    wdt_reset2          <= 1'b0
                        | wdt_reset0_vec_r // sync reset signal for timer 0
                        | wdt_parity_err;
  end
end


// spyglass disable_block Ac_conv01
// SMD:Reports signals from the same domain that are synchronized in the same destination domain and converge after any number of sequential elements
// SJ: These signals are synchronized first and aggregated together, these warnings can be ignored.
always @(posedge clk or posedge rst_a)  
begin
  if (rst_a==1'b1)
  begin : wdt_timeout_sigs_PRCO
    wdt_reset            <= 1'b0;
    wdt_reset_p1_r       <= 1'b0;   
    wdt_ext_timeout_r    <= 1'b0;
    wdt_ext_timeout_p1_r <= 1'b0; 
    wdt_ext0_timeout_r     <= 1'b0;
    wdt_ext0_timeout_r_r   <= 1'b0;    
    wdt_reset0_timeout_r   <= 1'b0;
    wdt_reset0_timeout_r_r <= 1'b0;   
  end
  else
  begin

      wdt_ext0_timeout_r <= wdt_ext0_timeout_vec_r; // sync external signal for timer 0
      wdt_ext0_timeout_r_r <= wdt_ext0_timeout_r;      

      wdt_reset0_timeout_r <= wdt_reset0_vec_r; // sync reset signal for timer 0
      wdt_reset0_timeout_r_r <= wdt_reset0_timeout_r;  
       

      wdt_reset_p1_r <= 
                       wdt_reset0_timeout_r_r | 
                        1'b0;

                                                      
     // Collect the external timout
     //
     wdt_ext_timeout_r <= (  
                          wdt_ext0_timeout_r_r |  
                          1'b0);

 // Add parity check for all registers   
 // spyglass disable_block Ac_glitch03
// spyglass enable_block Ac_glitch03

      wdt_reset <= 1'b0  
                   | parity_err_r            // parity register parity error
                   | wdt_reset_p1_r;         // timeout reset error  
                   
// spyglass enable_block Ac_conv01  
         
  end
 
end
// spyglass enable_block Ac_conv02

assign wdt_x3_stall = wdt_stall;

endmodule // watchdog
// PECSV wdt_control_p_err, wdt_period_cnt_p_err, wdt_period_p_err, wdt_lthresh_p_err, wdt_uthresh_p_err, wdt_enb_regs_p_err, 

