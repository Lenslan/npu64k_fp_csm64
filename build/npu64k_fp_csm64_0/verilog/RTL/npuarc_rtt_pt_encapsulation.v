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
//   rtt_pt_encapsulation
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
//   vpp +q +o rtt_pt_encapsulation.vpp
//
// ===========================================================================



`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_pt_encapsulation #(parameter PTM_WDT_PP = 120, parameter PC_PP = 31) (

rtt_clk,

sys_reset,
pt_sync_msg_i,
pt_en,
pr_num,
taddr,
rtt_uop_is_leave,
rtt_in_deslot,
rtt_in_eslot,
inst_commit,
unfiltered_inst_commit,
cond_valid,
cond_pass,
rtt_dslot,
branch,
branch_indir,
exception,
interrupt,
zd_loop,
timestamp,
resource_full,
ptc_msg_valid_i,
unfiltered_pc,
unfiltered_taddr,
pr_sel,

atb_syncreq,
cti_trace_en_dslot,  
pt_sbuf_en,
hist_trig,

i_cnt_a,
hist,

pt_sync_msg,
pt_msg_valid,
pt_msg

);

//leda NTL_CON32 off

input rtt_clk;

input sys_reset;
input pt_sync_msg_i;
input pt_en;
input [`npuarc_PRNUM_WDT-1:0] pr_num;
input [PC_PP-1:0] taddr;
input rtt_uop_is_leave;
input rtt_in_deslot;
input rtt_in_eslot;
input inst_commit;
input cond_valid;
input cond_pass;
input rtt_dslot;
input branch;
input branch_indir;
input exception;
input interrupt;
input zd_loop;
input [`npuarc_TSTAMP_WDT-1:0]timestamp;
input resource_full;
input ptc_msg_valid_i;
input  [PC_PP-1:0] unfiltered_pc;
input  unfiltered_inst_commit;
input [PC_PP-1:0] unfiltered_taddr;

output [`npuarc_I_CNT-1:0] i_cnt_a;
output [`npuarc_HIST_WDT-1:0] hist;

output pt_sync_msg;
output pt_msg_valid;
output [PTM_WDT_PP-1:0] pt_msg;
input pr_sel;
input atb_syncreq;
input cti_trace_en_dslot;
reg sync_msg_gen_syncreq;
input pt_sbuf_en;
input hist_trig;

reg [PC_PP-1:0] unfiltered_taddr_r;
reg [PC_PP-1:0] taddr_r;
reg [PTM_WDT_PP-1:0] pt_msg;
wire pt_msg_valid;
wire pt_msg_valid_i;
reg pt_msg_valid_r;
reg pt_msg_valid_dir_r;
wire sync_msg;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;
reg [4:0] sync;
wire [1:0] b_type;
wire [30:0] u_addr;
reg[`npuarc_I_CNT-1:0] i_cnt;
wire [`npuarc_I_CNT:0] i_cnt_xx;
wire [`npuarc_HIST_WDT-1:0] hist;
reg [`npuarc_HIST_WDT-1:0] hist_r;
wire [`npuarc_I_CNT-1:0] i_cnt_a;
wire [`npuarc_TSTAMP_WDT-1:0] time_stamp;

wire [7:0] pt_mdo_nons [11:0];
wire [7:0] pt_mdo_s    [11:0];
wire [1:0] pt_mseo_nons[11:0];
wire [1:0] pt_mseo_s   [11:0];

reg sync_msg_gen;
reg pt_en_r;
reg [`npuarc_SYNC_CNT_WDT-1:0] sync_counter;

reg  [PC_PP-1:0] unfiltered_pc_r;
reg  unfiltered_inst_commit_r;

wire pt_en_pos_edge;
reg rtt_uop_is_leave_r;
reg rtt_in_deslot_r;
reg rtt_in_eslot_r;
wire [`npuarc_I_CNT:0] i_cnt_a_xx;




/**************************************************/
//Registered version of unfiltered commit
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_INST_COMMIT_R_PROC
    if(sys_reset == 1'b1)
      unfiltered_inst_commit_r <= 1'b0;
    else
      unfiltered_inst_commit_r <= unfiltered_inst_commit;
  end

/**************************************************/
//Registered version of unfiltered PC value
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_PC_R_BLK_PROC
    if(sys_reset == 1'b1)
      unfiltered_pc_r <= 0;
    else
      unfiltered_pc_r <= unfiltered_pc;
  end

/**************************************************/
//Registered version of unfiltered branch target address
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : UNFIL_TADDR_R_PROC
    if(sys_reset == 1'b1)
      unfiltered_taddr_r <= 0;
    else
      unfiltered_taddr_r <= unfiltered_taddr;
  end

/**************************************************/
//Registered version of PT message enable signal
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : PT_EN_R_PROC
    if(sys_reset == 1'b1)
      pt_en_r <= 1'b0;
    else
      pt_en_r <= pt_en;
  end


assign pt_en_pos_edge = (!pt_en_r) && pt_en;

/**************************************************/
//Registered version of UOP sequence control signal
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_UOP_IS_LEAVE_R_PROC
    if(sys_reset == 1'b1)
      rtt_uop_is_leave_r <= 1'b0;
    else
      rtt_uop_is_leave_r <= rtt_uop_is_leave;
  end

/**************************************************/
//Registered version of delay slot control signal
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_IN_DESLOT_R_PROC
    if(sys_reset == 1'b1)
      rtt_in_deslot_r <= 1'b0;
    else
      rtt_in_deslot_r <= rtt_in_deslot;
  end

/**************************************************/
//Registered version of eslot control signal
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_IN_ESLOT_R_PROC
    if(sys_reset == 1'b1)
      rtt_in_eslot_r <= 1'b0;
    else
      rtt_in_eslot_r <= rtt_in_eslot;
  end


//leda BTTF_D002 off

// spyglass disable_block SelfDeterminedExpr-ML
/**************************************************/
//Sync_counter increaments by one for of the message sent and it gets reset when it
//sends sync message. The reason for sending sync message can be :
//1. pt_sync_msg_i - Recovery from message lose
//2. &sync_counter - Counter over flow
//3. evti - EVTI signal
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : SYNC_COUNTER_PROC
    if(sys_reset == 1'b1)
      sync_counter <= `npuarc_SYNC_CNT_WDT'b0;
    else if(pt_en_pos_edge || pt_sync_msg_i || ((&sync_counter) && pt_msg_valid) || atb_syncreq)
      sync_counter <= `npuarc_SYNC_CNT_WDT'b0;
    else if(pt_msg_valid)
      sync_counter <= {sync_counter + `npuarc_SYNC_CNT_WDT'b1};
  end
// spyglass enable_block SelfDeterminedExpr-ML

//leda BTTF_D002 on
/**************************************************/
//sync_msg_gen_syncreq is flag for generating SYNC message for SYNCREQ.
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : SYNC_MSG_SYNCREQ_PROC
    if(sys_reset == 1'b1)
      sync_msg_gen_syncreq <= 1'b0;
    else if(~pr_sel)
      sync_msg_gen_syncreq <= 1'b0;
    else if(atb_syncreq)
      sync_msg_gen_syncreq <= 1'b1;
    else if(pt_msg_valid && pt_sbuf_en)
      sync_msg_gen_syncreq <= 1'b0;
  end
/**************************************************/
//sync_msg_gen is flag for generating SYNC message for NON-EVTI.
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : SYNC_MSG_PROC
    if(sys_reset == 1'b1)
      sync_msg_gen <= 1'b1;
    else if(pt_en_pos_edge || pt_sync_msg_i || ((&sync_counter) && pt_msg_valid) || atb_syncreq)
      sync_msg_gen <= 1'b1;
    else if(pt_msg_valid)
      sync_msg_gen <= 1'b0;
  end
/**************************************************/
//This 'sync' bus gives SYNC value to be placed in the message.
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : SYNC_PROC
    if(sys_reset == 1'b1)
      sync <= 5'd1;
    else if(atb_syncreq)
      sync <= 5'd14;
    else if(pt_en_pos_edge && (!sync_msg_gen_syncreq))
      sync <= 5'd5;
    else if(pt_sync_msg_i && (!sync_msg_gen_syncreq))
      sync <= 5'd7;
    else if((&sync_counter) && pt_msg_valid)
      sync <= 5'd2;
  end

assign i_cnt_xx = (i_cnt + {{(`npuarc_I_CNT-1){1'b0}},inst_commit});

/**************************************************/
//i_cnt - Instruction counter
/**************************************************/
//leda BTTF_D002 off
always @ (posedge rtt_clk or posedge sys_reset)
  begin : I_CNT_PROC
    if(sys_reset == 1'b1)
      i_cnt <= `npuarc_I_CNT'b0;
    else if(pt_msg_valid || (resource_full && (&i_cnt_a)) || ptc_msg_valid_i)
      i_cnt <= `npuarc_I_CNT'b0;
    else if((inst_commit)  && (!interrupt) && (!pt_msg_valid))
      i_cnt <= i_cnt_xx[`npuarc_I_CNT-1:0];
  end

/*Source code for single issue core interface*/

//leda BTTF_D002 on
/**************************************************/
//hist_r - Branch history stored
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : HIST_PROC
    if(sys_reset == 1'b1)
      hist_r <= `npuarc_HIST_WDT'b1;
    else if(((!(pt_msg_valid || ptc_msg_valid_i)) && hist_trig) && inst_commit && (cond_valid && cond_pass) && ((branch && (!branch_indir)) || (branch && branch_indir && rtt_dslot) || (!branch)))
      hist_r <= `npuarc_HIST_WDT'b11;
    else if(((!(pt_msg_valid || ptc_msg_valid_i)) && hist_trig) && inst_commit && ((cond_valid && (!cond_pass) )) && (!(branch && branch_indir && (!rtt_dslot))))
      hist_r <= `npuarc_HIST_WDT'b10;
    else if ((pt_msg_valid_i && (!rtt_dslot)) || (pt_msg_valid_r && unfiltered_inst_commit_r && (taddr_r == unfiltered_pc_r)) || (resource_full && hist_trig) || ptc_msg_valid_i || (inst_commit && rtt_uop_is_leave_r && rtt_in_deslot_r))
      hist_r <= `npuarc_HIST_WDT'b1;
    else if(inst_commit && (cond_valid && cond_pass) && ((branch && (!branch_indir)) || (branch && branch_indir && rtt_dslot) || (!branch)))
      hist_r <= ({hist_r[30:0],1'b1} );
    else if(inst_commit && ((cond_valid && (!cond_pass) )) && (!(branch && branch_indir && (!rtt_dslot))))
      hist_r <= ({hist_r[30:0],1'b0} );
  end
/**************************************************/
//hist_r - Branch history in PT message
/**************************************************/
assign hist = ((pt_msg_valid_r && unfiltered_inst_commit_r && (taddr_r == unfiltered_pc_r)) && ((cond_valid && cond_pass) && ((branch && (!branch_indir)) || (branch && branch_indir && rtt_dslot) || (!branch)))) ?
              {hist_r[30:0],1'b1} :
              ((pt_msg_valid_r && unfiltered_inst_commit_r && (taddr_r == unfiltered_pc_r)) && (((cond_valid && (!cond_pass) )) && (!(branch && branch_indir && (!rtt_dslot))))) ?
              {hist_r[30:0],1'b0} :
              (inst_commit && (zd_loop || rtt_in_eslot_r) && cond_valid && cond_pass) ? {hist_r[30:0],1'b1} : (inst_commit && (zd_loop || rtt_in_eslot_r) && cond_valid && (!cond_pass)) ? {hist_r[30:0],1'b0} : hist_r;

//leda BTTF_D002 off
/**************************************************/
//i_cnt_a - Actual I-CNT in PT message
/**************************************************/
assign i_cnt_a = (inst_commit && (!interrupt) && (!exception)) ? (&i_cnt ? {`npuarc_I_CNT{1'b0}} : (i_cnt + {{(`npuarc_I_CNT-1){1'b0}},1'b1})) : i_cnt;
//leda BTTF_D002 on

assign pt_msg_valid_i = ((inst_commit && branch && branch_indir && ((!cond_valid) || (cond_valid && cond_pass))) || (inst_commit && (zd_loop || rtt_in_eslot_r)) || exception ||interrupt);
assign pt_msg_valid = ((pt_msg_valid_i && (!rtt_dslot)) || (pt_msg_valid_r && unfiltered_inst_commit_r && (taddr_r == unfiltered_pc_r)) || (inst_commit && rtt_uop_is_leave_r && rtt_in_deslot_r));
assign pt_sync_msg = sync_msg;
assign sync_msg = pt_en && sync_msg_gen;
assign tcode = sync_msg ? 6'd29 : 6'd28;
assign src = pr_num;
assign b_type = (exception || interrupt) ? 2'b01 : zd_loop ? 2'b10 : 2'b00 ;
generate if (PC_PP != 31) begin: pc_pad_1
assign u_addr = {{(31-PC_PP){1'b0}},taddr};
end else begin: pc_pad_0
assign u_addr = taddr;
end
endgenerate
assign time_stamp = timestamp;

always @ (posedge rtt_clk or posedge sys_reset)
  begin : PT_MSG_VALID_R_PROC
    if(sys_reset == 1'b1)
      pt_msg_valid_r <= 1'b0;
    else if((pt_msg_valid_r && unfiltered_inst_commit_r && (taddr_r == unfiltered_pc_r)) || (~cti_trace_en_dslot) || (~pr_sel))
      pt_msg_valid_r <= 1'b0;
    else if((pt_msg_valid_i && rtt_dslot) || (pt_msg_valid_dir_r && (exception || interrupt)))
      pt_msg_valid_r <= 1'b1;
  end

always @ (posedge rtt_clk or posedge sys_reset)
  begin : TADDR_R_PROC
    if(sys_reset == 1'b1)
      taddr_r <= 0;
    else if((pt_msg_valid_i || (inst_commit && branch && (!branch_indir) && ((!cond_valid) || (cond_valid && cond_pass))))&& rtt_dslot)
      taddr_r <= unfiltered_taddr_r;
  end


always @ (posedge rtt_clk or posedge sys_reset)
  begin : PT_MSG_VALID_DIR_R_PROC
    if(sys_reset == 1'b1)
      pt_msg_valid_dir_r <= 1'b0;
    else if((inst_commit && branch && (!branch_indir) && ((!cond_valid) || (cond_valid && cond_pass))) && rtt_dslot)
      pt_msg_valid_dir_r <= 1'b1;
    else if((!(exception || interrupt)) && inst_commit)
      pt_msg_valid_dir_r <= 1'b0;
  end




assign pt_mdo_nons[0] = {b_type[1:0],tcode[5:0]};
assign pt_mdo_nons[1] = {i_cnt_a[7:0]};
assign pt_mdo_nons[2] = u_addr[7:0];
assign pt_mdo_nons[3] = ~|u_addr[30:8]  ? hist[7:0] : u_addr[15:8];

assign pt_mdo_nons[4] = ~|u_addr[30:8]  ? (~|hist[31:8] ? time_stamp[7:0]:hist[15:8]) :
                        ~|u_addr[30:16] ?  hist[7:0] : u_addr[23:16];

assign pt_mdo_nons[5] = ~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? time_stamp[7:0] : hist[23:16]) :
                        ~|u_addr[30:16] ? (~|hist[31:8] ? time_stamp[7:0]:hist[15:8]):
                        ~|u_addr[30:24] ? hist[7:0] : {1'b0,u_addr[30:24]};

assign pt_mdo_nons[6] = ~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00  : ~|hist[31:24] ? time_stamp[7:0] :hist[31:24]) :
                        ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? time_stamp[7:0]: hist[23:16] ):
                        ~|u_addr[30:24] ? (~|hist[31:8] ? time_stamp[7:0] : hist[15:8]) : hist[7:0];

assign pt_mdo_nons[7] = ~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00  : ~|hist[31:24] ? 8'h00  : time_stamp[7:0]) :
                        ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24]? time_stamp[7:0]:  hist[31:24]):
                        ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  time_stamp[7:0] : hist[23:16]) :
                            (~|hist[31:8] ? time_stamp[7:0] : hist[15:8]);

assign pt_mdo_nons[8] = ~|u_addr[30:8] ? 8'h00 :
                        ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24]? 8'h00 :  time_stamp[7:0]):
                        ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  8'h00 : ~|hist[31:24] ? time_stamp[7:0] : hist[31:24]):
                            (~|hist[31:8] ? 8'h00 : (~|hist[31:16] ? time_stamp[7:0] : hist[23:16]));

assign pt_mdo_nons[9] = ~|u_addr[30:8]  ? 8'h00 :
                        ~|u_addr[30:16] ? 8'h00 :
                        ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  8'h00 : ~|hist[31:24] ? 8'h00 : time_stamp[7:0]):
                            (~|hist[31:8] ? 8'h00 : (~|hist[31:16] ? 8'h00 : (~|hist[31:24] ? time_stamp[7:0] : hist[31:24])));

assign pt_mdo_nons[10] = ~|u_addr[30:8]  ? 8'h00 :
                         ~|u_addr[30:16] ? 8'h00 :
                         ~|u_addr[30:24] ? 8'h00 :
                            (~|hist[31:8] ? 8'h00 : (~|hist[31:16] ? 8'h00 : (~|hist[31:24] ? 8'h00 : time_stamp[7:0])));
assign pt_mdo_nons[11] =  8'h00;


assign pt_mdo_s[0] = {sync[1:0],tcode[5:0]};
assign pt_mdo_s[1] = {i_cnt_a[2:0],b_type[1:0], sync[4:2]};
assign pt_mdo_s[2] = ~|i_cnt_a[7:3] ? u_addr[7:0]: {3'b0,i_cnt_a[7:3]};
assign pt_mdo_s[3] = ~|i_cnt_a[7:3] ? ~|u_addr[30:8] ? hist[7:0] : u_addr[15:8] : u_addr[7:0];

assign pt_mdo_s[4] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? (~|hist[31:8] ? time_stamp[7:0] : hist[15:8]) :
                                       ~|u_addr[30:16] ? hist[7:0] : u_addr[23:16]) :
                                      (~|u_addr[30:8]  ? hist[7:0] : u_addr[15:8]) ;

assign pt_mdo_s[5] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? time_stamp[7:0] : hist[23:16]) :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? time_stamp[7:0]:hist[15:8]):
                                       ~|u_addr[30:24] ? hist[7:0] : {1'b0,u_addr[30:24]}) :
                                      (~|u_addr[30:8]  ? (~|hist[31:8] ? time_stamp[7:0]:hist[15:8]) :
                                       ~|u_addr[30:16] ? hist[7:0] : u_addr[23:16]);

assign pt_mdo_s[6] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00  : ~|hist[31:24] ? time_stamp[7:0] :hist[31:24]) :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? time_stamp[7:0]: hist[23:16] ):
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? time_stamp[7:0] : hist[15:8]) : hist[7:0]) :
                                      (~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? time_stamp[7:0] : hist[23:16]) :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? time_stamp[7:0]:hist[15:8]):
                                       ~|u_addr[30:24] ? hist[7:0] : {1'b0,u_addr[30:24]});

assign pt_mdo_s[7] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00  : ~|hist[31:24] ? 8'h00  : time_stamp[7:0]) :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24]? time_stamp[7:0]:  hist[31:24]):
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  time_stamp[7:0] : hist[23:16]) :
                                        (~|hist[31:8]  ? time_stamp[7:0] : hist[15:8])) :
                                      (~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00  : ~|hist[31:24] ? time_stamp[7:0] :hist[31:24]) :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? time_stamp[7:0]: hist[23:16] ):
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? time_stamp[7:0] : hist[15:8]) : hist[7:0]);

assign pt_mdo_s[8] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? 8'h00 :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24]? 8'h00 :  time_stamp[7:0]):
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  8'h00 : ~|hist[31:24] ? time_stamp[7:0] : hist[31:24]):
                                        (~|hist[31:8]  ? 8'h00 : (~|hist[31:16] ? time_stamp[7:0] : hist[23:16]))) :
                                      (~|u_addr[30:8]  ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00  : ~|hist[31:24] ? 8'h00  : time_stamp[7:0]) :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24]? time_stamp[7:0]:  hist[31:24]):
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  time_stamp[7:0] : hist[23:16]) :
                                        (~|hist[31:8]  ? time_stamp[7:0] : hist[15:8]));
assign pt_mdo_s[9] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? 8'h00 :
                                       ~|u_addr[30:16] ? 8'h00 :
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  8'h00 : ~|hist[31:24] ? 8'h00 : time_stamp[7:0]):
                                        (~|hist[31:8]  ? 8'h00 : (~|hist[31:16] ? 8'h00 : (~|hist[31:24] ? time_stamp[7:0] : hist[31:24])))) :
                                      (~|u_addr[30:8]  ? 8'h00 :
                                       ~|u_addr[30:16] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24]? 8'h00 :  time_stamp[7:0]):
                                       ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ?  8'h00 : ~|hist[31:24] ? time_stamp[7:0] : hist[31:24]):
                                        (~|hist[31:8]  ? 8'h00 : (~|hist[31:16] ? time_stamp[7:0] : hist[23:16])));
assign pt_mdo_s[10] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8]  ? 8'h00 :
                                        ~|u_addr[30:16] ? 8'h00 :
                                        ~|u_addr[30:24] ? 8'h00 :
                                         (~|hist[31:8]  ? 8'h00 : (~|hist[31:16] ? 8'h00 : (~|hist[31:24] ? 8'h00 : time_stamp[7:0])))) :
                                       (~|u_addr[30:8]  ? 8'h00 :
                                        ~|u_addr[30:16] ? 8'h00 :
                                        ~|u_addr[30:24] ? (~|hist[31:8] ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24] ? 8'h00 : time_stamp[7:0]):
                                         (~|hist[31:8]  ? 8'h00 : ~|hist[31:16] ? 8'h00 : ~|hist[31:24] ? time_stamp[7:0] : hist[31:24]));
assign pt_mdo_s[11] = ~|i_cnt_a[7:3] ? 8'h00 :
                                       (~|u_addr[30:8]  ? 8'h00 :
                                        ~|u_addr[30:16] ? 8'h00 :
                                        ~|u_addr[30:24] ? 8'h00 :
                                        ~|hist[31:8]    ? 8'h00 : ~|hist[31:16] ?  8'h00 : ~|hist[31:24] ? 8'h00 : time_stamp[7:0]);


assign pt_mseo_nons[0] = 2'b00;
assign pt_mseo_nons[1] = 2'b01;
assign pt_mseo_nons[2] = ~|u_addr[30:8] ?  2'b01 : 2'b00;

assign pt_mseo_nons[3] =  ~|u_addr[30:8]  ? (~|hist[31:8]? 2'b01 :2'b00 ):
                          ~|u_addr[30:16] ? 2'b01 : 2'b00;

assign pt_mseo_nons[4] =  ~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b11 :(~|hist[31:16] ? 2'b01 : 2'b00)) :
                          ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b01 : 2'b00) :
                          ~|u_addr[30:24] ? 2'b01 : 2'b00;

assign pt_mseo_nons[5] =  ~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)) :
                          ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)):
                          ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b01 : 2'b00) : 2'b01;

assign pt_mseo_nons[6] =  ~|u_addr[30:8] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00  : ~|hist[31:24] ? 2'b11 :2'b01) :
                          ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11: (~|hist[31:24] ? 2'b01 : 2'b00) ):
                          ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)) :
                            (~|hist[31:8] ? 2'b01 : 2'b00);

assign pt_mseo_nons[7] =  ~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00 : ~|hist[31:24] ? 2'b00 : 2'b11) :
                          ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00 : ~|hist[31:24] ? 2'b11 : 2'b01) :
                          ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11 : ~|hist[31:24] ? 2'b01 : 2'b00) :
                            (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00));

assign pt_mseo_nons[8] =  ~|u_addr[30:8]  ? 2'b00:
                          ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00: ~|hist[31:24]? 2'b00:  2'b11):
                          ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00 : ~|hist[31:24] ? 2'b11 : 2'b01):
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)));

assign pt_mseo_nons[9] =  ~|u_addr[30:8]  ? 2'b00:
                          ~|u_addr[30:16] ? 2'b00:
                          ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ?  2'b00 : ~|hist[31:24] ? 2'b00 : 2'b11):
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b00 : (~|hist[31:24] ? 2'b11 : 2'b01)));
assign pt_mseo_nons[10] = ~|u_addr[30:8]  ? 2'b00:
                          ~|u_addr[30:16] ? 2'b00:
                          ~|u_addr[30:24] ? 2'b00:
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b00 : (~|hist[31:24] ? 2'b00 : 2'b11)));

assign pt_mseo_nons[11] = 2'b00;

assign pt_mseo_s[0] = 2'b00;
assign pt_mseo_s[1] = ~|i_cnt_a[7:3] ? 2'b01 : 2'b00;
assign pt_mseo_s[2] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8] ?  2'b01 : 2'b00) : 2'b01;
assign pt_mseo_s[3] = ~|i_cnt_a[7:3] ? (~|u_addr[30:8] ? (~|hist[31:8]? 2'b01 :2'b00 ): (~|u_addr[30:16] ? 2'b01 : 2'b00)) :
                          (~|u_addr[30:8] ?  2'b01 : 2'b00);

assign pt_mseo_s[4] = ~|i_cnt_a[7:3] ?
                          (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b11 :(~|hist[31:16] ? 2'b01 : 2'b00)) :
                           ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b01 : 2'b00) :
                            (~|u_addr[30:24] ? 2'b01 : 2'b00)) :
                          (~|u_addr[30:8] ? (~|hist[31:8]? 2'b01 :2'b00 ): (~|u_addr[30:16] ? 2'b01 : 2'b00));

assign pt_mseo_s[5] = ~|i_cnt_a[7:3] ?
                          (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)) :
                           ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)):
                           ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b01 : 2'b00) :
                                2'b01) :
                           (~|u_addr[30:8] ? (~|hist[31:8] ? 2'b11 :(~|hist[31:16] ? 2'b01 : 2'b00)) :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b01 : 2'b00) :
                            ~|u_addr[30:24] ? 2'b01 : 2'b00);

assign pt_mseo_s[6] = ~|i_cnt_a[7:3] ?
                           (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00  : ~|hist[31:24] ? 2'b11 :2'b01) :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11: (~|hist[31:24] ? 2'b01 : 2'b00) ):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)) :
                            (~|hist[31:8] ? 2'b01 : 2'b00)) :
                           (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)) :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b01 : 2'b00) :
                                2'b01) ;

assign pt_mseo_s[7] = ~|i_cnt_a[7:3] ?
                           (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00  : ~|hist[31:24] ?2'b00  : 2'b11) :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00: ~|hist[31:24]? 2'b11:  2'b01):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)) :
                            (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00))) :
                           (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00  : ~|hist[31:24] ? 2'b11 :2'b01) :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11: (~|hist[31:24] ? 2'b01 : 2'b00) ):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)) :
                            (~|hist[31:8] ? 2'b01 : 2'b00));

assign pt_mseo_s[8] = ~|i_cnt_a[7:3] ?
                           (~|u_addr[30:8]  ? 2'b00 :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00: ~|hist[31:24]? 2'b00:  2'b11):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ?  2'b00 : ~|hist[31:24] ? 2'b11 : 2'b01):
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)))) :
                           (~|u_addr[30:8]  ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00  : ~|hist[31:24] ?2'b00  : 2'b11) :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00: ~|hist[31:24]? 2'b11:  2'b01):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00)) :
                            (~|hist[31:8] ? 2'b11 : (~|hist[31:16] ? 2'b01 : 2'b00)));

assign pt_mseo_s[9] = ~|i_cnt_a[7:3] ?
                           (~|u_addr[30:8]  ? 2'b00 :
                            ~|u_addr[30:16] ? 2'b00:
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ?  2'b00 : ~|hist[31:24] ? 2'b00 : 2'b11):
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b00 : (~|hist[31:24] ? 2'b11 : 2'b01)))) :
                           (~|u_addr[30:8]  ? 2'b00 :
                            ~|u_addr[30:16] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ? 2'b00: ~|hist[31:24]? 2'b00:  2'b11):
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ?  2'b00 : ~|hist[31:24] ? 2'b11 : 2'b01):
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b11 : (~|hist[31:24] ? 2'b01 : 2'b00))));

assign pt_mseo_s[10] = ~|i_cnt_a[7:3] ?
                           (~|u_addr[30:8]  ? 2'b00:
                            ~|u_addr[30:16] ? 2'b00:
                            ~|u_addr[30:24] ? 2'b00:
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b00 : (~|hist[31:24] ? 2'b00 : 2'b11)))) :
                           (~|u_addr[30:8]  ? 2'b00 :
                            ~|u_addr[30:16] ? 2'b00:
                            ~|u_addr[30:24] ? (~|hist[31:8] ? 2'b00 : ~|hist[31:16] ?  2'b00 : ~|hist[31:24] ? 2'b00 : 2'b11):
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b00 : (~|hist[31:24] ? 2'b11 : 2'b01))));

assign pt_mseo_s[11] = ~|i_cnt_a[7:3] ? 2'b00 :
                           (~|u_addr[30:8]  ? 2'b00:
                            ~|u_addr[30:16] ? 2'b00:
                            ~|u_addr[30:24] ? 2'b00:
                            (~|hist[31:8] ? 2'b00 : (~|hist[31:16] ? 2'b00 : (~|hist[31:24] ? 2'b00 : 2'b11))));


always @*
  begin : PT_MSG_PROC
    if(sync_msg)
      begin
          pt_msg [7:0] = pt_mdo_s[0];
          pt_msg [17:10] = pt_mdo_s[1];
          pt_msg [27:20] = pt_mdo_s[2];
          pt_msg [37:30] = pt_mdo_s[3];
          pt_msg [47:40] = pt_mdo_s[4];
          pt_msg [57:50] = pt_mdo_s[5];
          pt_msg [67:60] = pt_mdo_s[6];
          pt_msg [77:70] = pt_mdo_s[7];
          pt_msg [87:80] = pt_mdo_s[8];
          pt_msg [97:90] = pt_mdo_s[9];
          pt_msg [107:100] = pt_mdo_s[10];
          pt_msg [117:110] = pt_mdo_s[11];
          pt_msg [9:8] = pt_mseo_s[0];
          pt_msg [19:18] = pt_mseo_s[1];
          pt_msg [29:28] = pt_mseo_s[2];
          pt_msg [39:38] = pt_mseo_s[3];
          pt_msg [49:48] = pt_mseo_s[4];
          pt_msg [59:58] = pt_mseo_s[5];
          pt_msg [69:68] = pt_mseo_s[6];
          pt_msg [79:78] = pt_mseo_s[7];
          pt_msg [89:88] = pt_mseo_s[8];
          pt_msg [99:98] = pt_mseo_s[9];
          pt_msg [109:108] = pt_mseo_s[10];
          pt_msg [119:118] = pt_mseo_s[11];
      end
    else
      begin
          pt_msg [7:0] = pt_mdo_nons[0];
          pt_msg [17:10] = pt_mdo_nons[1];
          pt_msg [27:20] = pt_mdo_nons[2];
          pt_msg [37:30] = pt_mdo_nons[3];
          pt_msg [47:40] = pt_mdo_nons[4];
          pt_msg [57:50] = pt_mdo_nons[5];
          pt_msg [67:60] = pt_mdo_nons[6];
          pt_msg [77:70] = pt_mdo_nons[7];
          pt_msg [87:80] = pt_mdo_nons[8];
          pt_msg [97:90] = pt_mdo_nons[9];
          pt_msg [107:100] = pt_mdo_nons[10];
          pt_msg [117:110] = pt_mdo_nons[11];
          pt_msg [9:8] = pt_mseo_nons[0];
          pt_msg [19:18] = pt_mseo_nons[1];
          pt_msg [29:28] = pt_mseo_nons[2];
          pt_msg [39:38] = pt_mseo_nons[3];
          pt_msg [49:48] = pt_mseo_nons[4];
          pt_msg [59:58] = pt_mseo_nons[5];
          pt_msg [69:68] = pt_mseo_nons[6];
          pt_msg [79:78] = pt_mseo_nons[7];
          pt_msg [89:88] = pt_mseo_nons[8];
          pt_msg [99:98] = pt_mseo_nons[9];
          pt_msg [109:108] = pt_mseo_nons[10];
          pt_msg [119:118] = pt_mseo_nons[11];
      end
  end

//leda NTL_CON32 on
endmodule
