// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   rtt_ptc_encapsulation
//
// ===========================================================================
//
// Description:
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_ptc_encapsulation.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_ptc_encapsulation #(parameter PTCM_WDT_PP = 120, parameter PC_PP = 31) (

rtt_clk,

sys_reset,
pr_num,

i_cnt,
hist,

exception    ,
interrupt    ,
zd_loop      ,
unfilter_exception    ,
unfilter_interrupt    ,
unfilter_zd_loop      ,
pr0_inst_commit,
unfiltered_inst_commit,
unfiltered_relative_pc,
pc_msg_valid,
flush_cmd,
flush_done,
filter_busy,
compressor_busy,
sbuf_empty,
active_prdcr,

timestamp,

ptc_msg_valid_r,
ptc_msg_valid,
ptc_msg_valid_i,
ptc_msg

);

input rtt_clk;

input sys_reset;
input [`npuarc_PRNUM_WDT-1:0] pr_num;

input [`npuarc_I_CNT-1:0] i_cnt;
input [`npuarc_HIST_WDT-1:0] hist;
input                        exception    ;
input                        interrupt    ;
input                        zd_loop      ;
input                        unfilter_exception    ;
input                        unfilter_interrupt    ;
input                        unfilter_zd_loop      ;
input pr0_inst_commit;
input unfiltered_inst_commit;
input  [PC_PP-1:0]              unfiltered_relative_pc;

input pc_msg_valid;
input flush_cmd;
input flush_done;
input filter_busy;
input compressor_busy;
input sbuf_empty;
input active_prdcr;

input [`npuarc_TSTAMP_WDT-1:0]timestamp;

output ptc_msg_valid_r;
output ptc_msg_valid;
output ptc_msg_valid_i;
output [PTCM_WDT_PP-1:0] ptc_msg;

reg [PTCM_WDT_PP-1:0] ptc_msg;

wire ptc_msg_valid;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;
wire [`npuarc_TSTAMP_WDT-1:0] time_stamp;

wire [7:0] ptcm_mdo [11:0];
wire [1:0] ptcm_mseo[11:0];

reg flush;
reg ptc_msg_valid_r;
reg pc_msg_valid_st;
wire [3:0] evcode;
wire [31:0] cdata1;
wire [1:0] cdf;
wire ptc_msg_valid_i;

reg unfiltered_inst_commit_r;
reg  [PC_PP-1:0] unfiltered_relative_pc_r;
reg unfiltered_exception_r;
reg unfiltered_interrupt_r;
reg unfiltered_zd_loop_r;

wire [30:0] cdata2;

always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_INST_COMMIT_R_PROC
    if(sys_reset == 1'b1)
      unfiltered_inst_commit_r <= 1'b0;
    else
      unfiltered_inst_commit_r <= unfiltered_inst_commit;
  end

always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_EXCEPTION_R_PROC
    if(sys_reset == 1'b1)
      unfiltered_exception_r <= 1'b0;
    else
      unfiltered_exception_r <= unfilter_exception;
  end

always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_INTERRUPT_R_PROC
    if(sys_reset == 1'b1)
      unfiltered_interrupt_r <= 1'b0;
    else
      unfiltered_interrupt_r <= unfilter_interrupt;
  end

always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_ZD_LOOP_R_PROC
    if(sys_reset == 1'b1)
      unfiltered_zd_loop_r <= 1'b0;
    else
      unfiltered_zd_loop_r <= (unfilter_zd_loop && unfiltered_inst_commit);
  end

always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_RELATIVE_PC_R_BLK_PROC
    if(sys_reset == 1'b1)
      unfiltered_relative_pc_r <= 0;
    else
      unfiltered_relative_pc_r <= unfiltered_relative_pc;
  end


/**************************************************/
//Program Trace correlation message valid
//Conditions for PTC generation :
//1. For each PC message a corresponding PTC message will be sent
//   When PC doesn't fall in the filter range
//2. When flush is issues and no pending messages with RTT
/**************************************************/
assign ptc_msg_valid_i =  ((((!pr0_inst_commit) && unfiltered_inst_commit_r) ||
                          ((!exception) && unfiltered_exception_r) ||
                          ((!interrupt) && unfiltered_interrupt_r) ||
                          ((!(zd_loop && pr0_inst_commit)) && unfiltered_zd_loop_r)
                         ) && pc_msg_valid_st) || (
                        flush &&
                        sbuf_empty && (!filter_busy) && (!compressor_busy) && (!ptc_msg_valid_r) && active_prdcr);

assign ptc_msg_valid = ptc_msg_valid_i;


//Message type encoding
assign tcode = 6'd33;

//Core/Producer number in multi-core configuration
assign src = pr_num;
assign time_stamp = timestamp;


//Correlation fields
assign cdata1 = hist;
assign cdata2 = (flush &&
                 sbuf_empty && (!filter_busy) && (!compressor_busy) && (!ptc_msg_valid_r)) ? 0 : unfiltered_relative_pc_r;


//Event code value for PTC message, Hard-coded to vendor-defined.
assign evcode = 4'b1000;

//Indicates the number of CDATA fields present in the message
assign cdf = 2'b10;


/**************************************************/
//flush - flag to indicate active flush operation
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : FLUSH_PROC
    if(sys_reset == 1'b1)
      flush <= 1'b0;
    else if(flush_done)
      flush <= 1'b0;
    else if(flush_cmd)
      flush <= 1'b1;
  end


/**************************************************/
//pc_msg_valid_st - flag to indicate PTC corresponding
// to PC message is pending
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : PC_MSG_VALID_ST_PROC
    if(sys_reset == 1'b1)
      pc_msg_valid_st <= 1'b0;
    else if(ptc_msg_valid_i)
      pc_msg_valid_st <= 1'b0;
    else if(pc_msg_valid)
      pc_msg_valid_st <= 1'b1;
  end


/**************************************************/
//ptc_msg_valid_r - flag to indicate PTC corresponding
// to flush is issued. This flag will be cleared
// when flush_done is high i.e. no messages pending with RTT
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : PTC_MSG_VALID_R_PROC
    if(sys_reset == 1'b1)
      ptc_msg_valid_r <= 1'b0;
    else if(flush_done)
      ptc_msg_valid_r <= 1'b0;
    else if(
            flush &&
            sbuf_empty && (!filter_busy) && (!compressor_busy) && (!ptc_msg_valid_r))
      ptc_msg_valid_r <= 1'b1;
  end

//---------------------
//PROGRAM TRACE CORRELATION MESSAGE
//---------------------

assign ptcm_mdo[0] = {evcode[1:0],tcode[5:0]};
assign ptcm_mdo[1] = {i_cnt[3:0],cdf[1:0],evcode[3:2]};
assign ptcm_mdo[2] = ~|i_cnt[7:4] ? cdata1[7:0] : {4'b0,i_cnt[7:4]};
assign ptcm_mdo[3] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ? cdata2[7:0] : cdata1[15:8]) : cdata1[7:0];

assign ptcm_mdo[4] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? time_stamp[7:0]:cdata2[15:8]) :
                                 ~|cdata1[31:16] ?
                                 cdata2[7:0] :
                                 cdata1[23:16]) : (~|cdata1[31:8] ? cdata2[7:0] : cdata1[15:8]) ;
assign ptcm_mdo[5] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? time_stamp[7:0] : cdata2[23:16]) :
                                 ~|cdata1[31:16] ?
                                (~|cdata2[30:8] ? time_stamp[7:0]:cdata2[15:8]):
                                 ~|cdata1[31:24] ?
                                cdata2[7:0] :
                                cdata1[31:24]) :
                                ( (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? time_stamp[7:0]:cdata2[15:8]) :
                                 ~|cdata1[31:16] ?
                                 cdata2[7:0] :
                                 cdata1[23:16]));
assign ptcm_mdo[6] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? time_stamp[7:0] :{1'b0,cdata2[30:24]}) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? time_stamp[7:0]: cdata2[23:16] ):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? time_stamp[7:0] : cdata2[15:8]) :
                            cdata2[7:0]) :
                            (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? time_stamp[7:0] : cdata2[23:16]) :
                                 ~|cdata1[31:16] ?
                                (~|cdata2[30:8] ? time_stamp[7:0]:cdata2[15:8]):
                                 ~|cdata1[31:24] ?
                                cdata2[7:0] :
                                cdata1[31:24]);
assign ptcm_mdo[7] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : time_stamp[7:0]) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? time_stamp[7:0]:  {1'b0,cdata2[30:24]}):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  time_stamp[7:0] : cdata2[23:16]) :
                            (~|cdata2[30:8] ? time_stamp[7:0] : cdata2[15:8])) :
                            (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? time_stamp[7:0] :{1'b0,cdata2[30:24]}) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? time_stamp[7:0]: cdata2[23:16] ):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? time_stamp[7:0] : cdata2[15:8]) :
                            cdata2[7:0]);
assign ptcm_mdo[8] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : 8'h00) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? 8'h00 :  time_stamp[7:0]):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? time_stamp[7:0] : {1'b0,cdata2[30:24]}):
                            (~|cdata2[30:8] ? 8'h00 : (~|cdata2[30:16] ? time_stamp[7:0] : cdata2[23:16]))) :
                            (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : time_stamp[7:0]) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? time_stamp[7:0]:  {1'b0,cdata2[30:24]}):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  time_stamp[7:0] : cdata2[23:16]) :
                            (~|cdata2[30:8] ? time_stamp[7:0] : cdata2[15:8]));
assign ptcm_mdo[9] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : 8'h00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? 8'h00 :  8'h00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? 8'h00 : time_stamp[7:0]):
                            (~|cdata2[30:8] ? 8'h00 : (~|cdata2[30:16] ? 8'h00 : (~|cdata2[30:24] ? time_stamp[7:0] : {1'b0,cdata2[30:24]})))) :
                            (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : 8'h00) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? 8'h00 :  time_stamp[7:0]):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? time_stamp[7:0] : {1'b0,cdata2[30:24]}):
                            (~|cdata2[30:8] ? 8'h00 : (~|cdata2[30:16] ? time_stamp[7:0] : cdata2[23:16])));
assign ptcm_mdo[10] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : 8'h00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? 8'h00 :  8'h00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? 8'h00 : 8'h00):
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? 8'h00: time_stamp[7:0])) :
                            (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : 8'h00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? 8'h00 :  8'h00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? 8'h00 : time_stamp[7:0]):
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? time_stamp[7:0] : {1'b0,cdata2[30:24]}));
assign ptcm_mdo[11] = ~|i_cnt[7:4] ? 8'h00 :
                           (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00  : ~|cdata2[30:24] ? 8'h00  : 8'h00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ? 8'h00 : ~|cdata2[30:24]? 8'h00 :  8'h00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? 8'h00 : 8'h00):
                            (~|cdata2[30:8] ? 8'h00 : ~|cdata2[30:16] ?  8'h00 : ~|cdata2[30:24] ? 8'h00 : time_stamp[7:0]));


assign ptcm_mseo[0] = 2'b00;
assign ptcm_mseo[1] = ~|i_cnt[7:4] ? 2'b01 : 2'b00;
assign ptcm_mseo[2] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ?  2'b01 : 2'b00) : 2'b01;
assign ptcm_mseo[3] = ~|i_cnt[7:4] ? (~|cdata1[31:8] ? (~|cdata2[30:8]? 2'b01 :2'b00 ): (~|cdata1[31:16] ? 2'b01 : 2'b00)) :
                          (~|cdata1[31:8] ?  2'b01 : 2'b00);

assign ptcm_mseo[4] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? 2'b11 :(~|cdata2[30:16] ? 2'b01 : 2'b00)) :
                                 ~|cdata1[31:16] ?
                                 (~|cdata2[30:8] ? 2'b01 : 2'b00) :
                                 (~|cdata1[31:24] ? 2'b01 : 2'b00)) :
                            (~|cdata1[31:8] ? (~|cdata2[30:8]? 2'b01 :2'b00 ): (~|cdata1[31:16] ? 2'b01 : 2'b00));
assign ptcm_mseo[5] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b11 : (~|cdata2[30:24] ? 2'b01 : 2'b00)) :
                                 ~|cdata1[31:16] ?
                                (~|cdata2[30:8] ? 2'b11 : (~|cdata2[30:16] ? 2'b01 : 2'b00)):
                                 ~|cdata1[31:24] ?
                                (~|cdata2[30:8] ? 2'b01 : 2'b00) :
                                2'b01) :
                           (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? 2'b11 :(~|cdata2[30:16] ? 2'b01 : 2'b00)) :
                                 ~|cdata1[31:16] ?
                                 (~|cdata2[30:8] ? 2'b01 : 2'b00) :
                                 (~|cdata1[31:24] ? 2'b01 : 2'b00));
assign ptcm_mseo[6] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b11 :2'b01) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b11: (~|cdata2[30:24] ? 2'b01 : 2'b00) ):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b11 : (~|cdata2[30:16] ? 2'b01 : 2'b00)) :
                            (~|cdata2[30:8] ? 2'b01 : 2'b00)) :
                           (~|cdata1[31:8] ?
                                 (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b11 : (~|cdata2[30:24] ? 2'b01 : 2'b00)) :
                                 ~|cdata1[31:16] ?
                                (~|cdata2[30:8] ? 2'b11 : (~|cdata2[30:16] ? 2'b01 : 2'b00)):
                                 ~|cdata1[31:24] ?
                                (~|cdata2[30:8] ? 2'b01 : 2'b00) :
                                2'b01) ;
assign ptcm_mseo[7] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ?2'b00  : 2'b11) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b11:  2'b01):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b11 : (~|cdata2[30:24] ? 2'b01 : 2'b00)) :
                            (~|cdata2[30:8] ? 2'b11 : (~|cdata2[30:16] ? 2'b01 : 2'b00))) :
                           (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b11 :2'b01) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b11: (~|cdata2[30:24] ? 2'b01 : 2'b00) ):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b11 : (~|cdata2[30:16] ? 2'b01 : 2'b00)) :
                            (~|cdata2[30:8] ? 2'b01 : 2'b00));
assign ptcm_mseo[8] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b00  : 2'b00) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b00:  2'b11):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ?  2'b00 : ~|cdata2[30:24] ? 2'b11 : 2'b01):
                            (~|cdata2[30:8] ? 2'b00 : (~|cdata2[30:16] ? 2'b11 : (~|cdata2[30:24] ? 2'b01 : 2'b00)))) :
                          (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ?2'b00  : 2'b11) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b11:  2'b01):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b11 : (~|cdata2[30:24] ? 2'b01 : 2'b00)) :
                            (~|cdata2[30:8] ? 2'b11 : (~|cdata2[30:16] ? 2'b01 : 2'b00)));
assign ptcm_mseo[9] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b00  : 2'b00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b00:  2'b00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ?  2'b00 : ~|cdata2[30:24] ? 2'b00 : 2'b11):
                            (~|cdata2[30:8] ? 2'b00 : (~|cdata2[30:16] ? 2'b00 : (~|cdata2[30:24] ? 2'b11 : 2'b01)))) :
                           (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b00  : 2'b00) :
                           ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b00:  2'b11):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ?  2'b00 : ~|cdata2[30:24] ? 2'b11 : 2'b01):
                            (~|cdata2[30:8] ? 2'b00 : (~|cdata2[30:16] ? 2'b11 : (~|cdata2[30:24] ? 2'b01 : 2'b00))));
assign ptcm_mseo[10] = ~|i_cnt[7:4] ?
                          (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b00  : 2'b00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b00:  2'b00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ?  2'b00 : ~|cdata2[30:24] ? 2'b00 : 2'b00):
                            (~|cdata2[30:8] ? 2'b00 : (~|cdata2[30:16] ? 2'b00 : (~|cdata2[30:24] ? 2'b00 : 2'b11)))) :
                           (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b00  : 2'b00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b00:  2'b00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ?  2'b00 : ~|cdata2[30:24] ? 2'b00 : 2'b11):
                            (~|cdata2[30:8] ? 2'b00 : (~|cdata2[30:16] ? 2'b00 : (~|cdata2[30:24] ? 2'b11 : 2'b01))));

assign ptcm_mseo[11] = ~|i_cnt[7:4] ? 0 :
                           (~|cdata1[31:8] ?
                           (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00  : ~|cdata2[30:24] ? 2'b00  : 2'b00) :
                            ~|cdata1[31:16] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ? 2'b00: ~|cdata2[30:24]? 2'b00:  2'b00):
                            ~|cdata1[31:24] ?
                            (~|cdata2[30:8] ? 2'b00 : ~|cdata2[30:16] ?  2'b00 : ~|cdata2[30:24] ? 2'b00 : 2'b00):
                            (~|cdata2[30:8] ? 2'b00 : (~|cdata2[30:16] ? 2'b00 : (~|cdata2[30:24] ? 2'b00 : 2'b11))));

always @*
  begin : PC_MSG_PROC
    ptc_msg [7:0] = ptcm_mdo[0];
    ptc_msg [17:10] = ptcm_mdo[1];
    ptc_msg [27:20] = ptcm_mdo[2];
    ptc_msg [37:30] = ptcm_mdo[3];
    ptc_msg [47:40] = ptcm_mdo[4];
    ptc_msg [57:50] = ptcm_mdo[5];
    ptc_msg [67:60] = ptcm_mdo[6];
    ptc_msg [77:70] = ptcm_mdo[7];
    ptc_msg [87:80] = ptcm_mdo[8];
    ptc_msg [97:90] = ptcm_mdo[9];
    ptc_msg [107:100] = ptcm_mdo[10];
    ptc_msg [117:110] = ptcm_mdo[11];
    ptc_msg [9:8] = ptcm_mseo[0];
    ptc_msg [19:18] = ptcm_mseo[1];
    ptc_msg [29:28] = ptcm_mseo[2];
    ptc_msg [39:38] = ptcm_mseo[3];
    ptc_msg [49:48] = ptcm_mseo[4];
    ptc_msg [59:58] = ptcm_mseo[5];
    ptc_msg [69:68] = ptcm_mseo[6];
    ptc_msg [79:78] = ptcm_mseo[7];
    ptc_msg [89:88] = ptcm_mseo[8];
    ptc_msg [99:98] = ptcm_mseo[9];
    ptc_msg [109:108] = ptcm_mseo[10];
    ptc_msg [119:118] = ptcm_mseo[11];
  end

endmodule
