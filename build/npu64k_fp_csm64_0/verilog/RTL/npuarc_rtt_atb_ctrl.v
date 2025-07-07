// Library ARC_Trace-3.0.999999999
// Copyright (C) 2016 Synopsys, Inc. All rights reserved.
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
//   rtt_atb_ctrl
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_atb_ctrl.vpp
//
// ===========================================================================
`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_atb_ctrl (
  has_rtt_iso_disable, 
        ug_rtt_clk,
  rtt_clk,
        rst_a,
        atid_in,
        ds_en,
        wr_data,
        wr_en,
        fifo_full,
        dsuppress,
        rttsyncreq,
        rtt_flush_command,
        para_done,
        atb_done,
        atb_ctrl_busy,
        atb_syncrfr,
        atclken,
        atresetn,
        syncreq,
        atready,
        afvalid,
        atvalid,
        atdata,
        atid,
        atbytes,
        afready
        );

parameter ATWDTH= 32;

localparam IDLE= 2'b00;
localparam DO_1ST_PKT= 2'b01;
localparam DO_NTH_PKT= 2'b10;
localparam DO_SYNC_PKT= 2'b11;

localparam RTTSYNC_PACKET = 32'hFFFF_FFFF;
localparam FIFOCOUNT_WDT = ((`npuarc_ATB_FIFO_DEPTH+1>256)?((`npuarc_ATB_FIFO_DEPTH+1>4096)?((`npuarc_ATB_FIFO_DEPTH+1>16384)?((`npuarc_ATB_FIFO_DEPTH+1>32768)?16:15):((`npuarc_ATB_FIFO_DEPTH+1>8192)?14:13)):((`npuarc_ATB_FIFO_DEPTH+1>1024)?((`npuarc_ATB_FIFO_DEPTH+1>2048)?12:11):((`npuarc_ATB_FIFO_DEPTH+1>512)?10:9))):((`npuarc_ATB_FIFO_DEPTH+1>16)?((`npuarc_ATB_FIFO_DEPTH+1>64)?((`npuarc_ATB_FIFO_DEPTH+1>128)?8:7):((`npuarc_ATB_FIFO_DEPTH+1>32)?6:5)):((`npuarc_ATB_FIFO_DEPTH+1>4)?((`npuarc_ATB_FIFO_DEPTH+1>8)?4:3):((`npuarc_ATB_FIFO_DEPTH+1>2)?2:1))));

input has_rtt_iso_disable; 

input ug_rtt_clk;
input rtt_clk;
input rst_a;
input [6:0] atid_in;
input ds_en;
input [120-1:0] wr_data;
input wr_en;
output fifo_full;
output dsuppress;
output rttsyncreq;
input rtt_flush_command;
input  para_done;
output atb_done;
output atb_ctrl_busy;
input [`npuarc_SYNCRFR_WDT-1:0] atb_syncrfr;

input atclken;
input atresetn;
input syncreq;
input atready;
input afvalid;
output atvalid;
output [ATWDTH-1:0] atdata;
output [6:0] atid;
output [`npuarc_ATBYTE_WIDTH-1:0] atbytes;
output afready;

wire [`npuarc_ATBYTE_WIDTH-1:0] atbytes;
reg        atbytes_msb;
wire [6:0] atid;

reg  [ATWDTH-1:0] atdata;
reg  atvalid;
reg  afready;

wire [ATWDTH-1:0] atdata_ns;
wire afready_ns;
reg  [1:0] fsm;
wire [1:0] fsm_var;

reg  [7:0] flushreq_cntr;
wire [7:0] flushreq_cntr_ns;
wire flushreq_cntr_rld;
wire afvalid_ns;
reg  afvalid_r;

wire [120-1:0] rdata;
wire [120-1:0] wr_data;

reg  [(120-2*30)-1:0] rdata_r;
wire [(120-2*30)-1:0] rdata_ns;
wire last_packet;
wire rd_req;
wire wr_en;
wire nwr_en_qual;

wire [FIFOCOUNT_WDT-1:0] pop_count;
wire [FIFOCOUNT_WDT-1:0] push_count;
reg  send_sync_req;
wire send_sync_req_ns;
wire fifo_full;
wire push_af_pipe;
reg  push_af_pipe_d1;
wire fifo_empty;
wire push_af;
wire push_hf;
reg  dsuppress;
wire dsuppress_ns;
wire rttsyncreq;
reg  rttsyncreq_r1;
reg  rttsyncreq_r2;
reg  [3:0] fsm_isidle;
wire [3:0] fsm_isidle_ns;
wire para_done;
reg  atb_done;
reg  msg_cntr_ovf_d;
reg  [`npuarc_SYNCRFR_WDT-1:0] atb_syncr_cnt;
reg  msg_cntr_ovf;
wire msg_cntr_ovf_ns;
wire [`npuarc_SYNCRFR_WDT-1:0] atb_syncr_cnt_ns;
wire periodic_syncr;
wire atb_syncr_ld;
reg [`npuarc_SYNCRFR_WDT-1:0] atb_syncrfr_r;
reg [`npuarc_SYNCRFR_WDT-1:0] atb_syncrfr_r2;
wire atb_ctrl_busy;

assign atb_ctrl_busy = ((|push_count) || (|pop_count) || (fsm!=IDLE));

assign push_af = (push_count>11);


//RTT Flush
//=========================================================
always @(posedge rtt_clk or posedge rst_a)
begin: PARA_DONE_REG
  if (rst_a)
    atb_done <=1'b0;
  else if (atb_done)
    atb_done <= 1'b0;
  else if (para_done)
    atb_done <= (~|push_count && ~|pop_count && (&fsm_isidle));
end


//ATB Flush
//=========================================================
assign afvalid_ns = (afvalid && ~afready);              // detect rising edge as well as back to back afvalids
assign flushreq_cntr_rld = afvalid && (~afvalid_r);
assign flushreq_cntr_ns =  flushreq_cntr_rld ? pop_count : flushreq_cntr - {{(FIFOCOUNT_WDT-1){1'b0}},(atready && (fsm!=IDLE))};
assign afready_ns = (~|flushreq_cntr_ns) && afvalid;


always @ (posedge ug_rtt_clk or negedge atresetn)
  begin : atb_flush
    if(!atresetn) begin
        afvalid_r       <= 1'b0;
        flushreq_cntr   <= {FIFOCOUNT_WDT{1'b0}};
        afready         <= 1'b0;
    end
    else if (has_rtt_iso_disable == 1'b0) begin
        afvalid_r       <= 1'b0;
        flushreq_cntr   <= {FIFOCOUNT_WDT{1'b0}};
        afready         <= 1'b1;
    end
    else if (atclken) begin
        afvalid_r       <= afvalid_ns;
        flushreq_cntr   <= flushreq_cntr_ns;
        afready         <= afready_ns;
    end
end

//Data suppress control
//=========================================================
assign dsuppress_ns = (dsuppress && (ds_en && push_hf)) || (ds_en && push_af);

always @ (posedge rtt_clk or posedge rst_a)
begin : dsuppress_proc
  if(rst_a) begin
    dsuppress <= 1'b0;
  end
  else begin
    dsuppress <= dsuppress_ns;
  end
end

always @ (posedge rtt_clk or negedge atresetn)
begin : RTTSYNCREQ_REG
  if(!atresetn)
    rttsyncreq_r1 <= 1'b0;
    else if (atclken)
    rttsyncreq_r1 <= ((fsm==DO_SYNC_PKT) && atready);
end

always @ (posedge rtt_clk or posedge rst_a)
begin : RTTSYNCREQ_D1
  if(rst_a)
    rttsyncreq_r2<= 1'b0;
  else
    rttsyncreq_r2<= rttsyncreq_r1;
end

assign rttsyncreq = rttsyncreq_r1  && ~rttsyncreq_r2;

wire [4:0] fsm_isidle_pre;
assign fsm_isidle_pre = (para_done && (fsm==IDLE)) ? (fsm_isidle + {3'b0,(~&fsm_isidle)}) : 5'b0;
assign fsm_isidle_ns = fsm_isidle_pre[3:0];

always @ (posedge rtt_clk or negedge atresetn)
begin : FSMIDLE_REG
  if(!atresetn)
    fsm_isidle <= 4'b0;
    else if (atclken)
    fsm_isidle <= fsm_isidle_ns;
end

always @ (posedge rtt_clk or negedge atresetn)
  begin : ATB_SYNCRFR_R_REG
    if(!atresetn) begin
      atb_syncrfr_r  <= {`npuarc_SYNCRFR_WDT{1'b0}};
      atb_syncrfr_r2 <= {`npuarc_SYNCRFR_WDT{1'b0}};
    end
    else if (atclken)
    begin // load new value
      atb_syncrfr_r2 <= atb_syncrfr_r;
      atb_syncrfr_r  <= atb_syncrfr;
    end
  end
assign atb_syncr_ld = (atb_syncrfr_r != atb_syncrfr_r2);

assign atb_syncr_cnt_ns  = atbytes_msb ?((atb_syncr_cnt >  16'd8) ? atb_syncr_cnt - 16'd8 :
                                         (atb_syncr_cnt == 16'd8) ? atb_syncrfr_r :
                                         (atb_syncr_cnt <  16'd8 && atb_syncr_cnt >  16'd1) ? atb_syncrfr_r - 16'd8 + atb_syncr_cnt : atb_syncrfr_r - 16'd7):
                                         ((atb_syncr_cnt >  16'd4) ? atb_syncr_cnt - 16'd4 :
                                         (atb_syncr_cnt == 16'd4) ? atb_syncrfr_r :
                                         (atb_syncr_cnt <  16'd4 && atb_syncr_cnt >  16'd1) ? atb_syncrfr_r - 16'd4 + atb_syncr_cnt : atb_syncrfr_r - 16'd3);

assign msg_cntr_ovf_ns  = atbytes_msb ? ~(atb_syncr_cnt >  16'd8): ~(atb_syncr_cnt >  16'd4);

always @ (posedge rtt_clk or negedge atresetn)
  begin : SYNCR_CNTR_REG
    if(!atresetn)
      atb_syncr_cnt <= {`npuarc_SYNCRFR_WDT{1'b0}};
    else if (atclken && (rtt_flush_command || atb_syncr_ld)) // load new value
      atb_syncr_cnt <= atb_syncrfr;
   else if (atclken && (atb_syncrfr<8)) // periodic syncreq disabled
      atb_syncr_cnt <= {`npuarc_SYNCRFR_WDT{1'b0}};
    else if (atclken && |atb_syncr_cnt && atready && atvalid)
      atb_syncr_cnt <= atb_syncr_cnt_ns;
  end
always @ (posedge rtt_clk or negedge atresetn)
  begin : MSG_CNTR_OVF_REG
    if(!atresetn)
      msg_cntr_ovf <= 1'b0;
else if (atclken && (rtt_flush_command || (atb_syncrfr<8))) // periodic syncreq disabled
      msg_cntr_ovf <= 1'b0;
    else if (atclken && |atb_syncr_cnt && atready && atvalid)
      msg_cntr_ovf <= msg_cntr_ovf_ns;
  end
assign periodic_syncr =  ~rtt_flush_command && (msg_cntr_ovf && ~msg_cntr_ovf_d);

//Data flow control
//=========================================================
assign atid = atid_in;          // pass-thru from rtt programming reg
assign last_packet = &rdata_r;
assign rdata_ns = last_packet ? rdata[120-1:2*30] : {2*30{1'b1}};
assign atdata_ns  = last_packet ? {rdata[59:45],1'b0,rdata[44:30],1'b0,rdata[29:15],1'b0,rdata[14:0],1'b0} : {rdata_r[59:45],1'b0,rdata_r[44:30],1'b0,rdata_r[29:15],1'b0,rdata_r[14:0],1'b0};
assign atbytes = has_rtt_iso_disable ? {atbytes_msb,2'b11}:3'b0;
assign send_sync_req_ns = (syncreq && !(send_sync_req && (fsm==DO_SYNC_PKT) && atready)) || (periodic_syncr & ~send_sync_req) || (send_sync_req && !((fsm==DO_SYNC_PKT) && atready));
assign rd_req = ~fifo_empty && (((fsm==IDLE) && ~atvalid) ||
                                ((fsm==DO_SYNC_PKT) && atready) ||
                                ((fsm==DO_1ST_PKT) && atready && last_packet && ~(send_sync_req)) ||
                                ((fsm==DO_NTH_PKT) && atready && last_packet && ~(send_sync_req)));

always @ (posedge rtt_clk or negedge atresetn)
begin : send_sync_proc
  if(!atresetn) begin
    send_sync_req <= 1'b0;
  end
    else if (atclken) begin
    send_sync_req <= send_sync_req_ns;
  end
end

always @ (posedge rtt_clk or negedge atresetn)
begin : edged_msgcntr_proc
  if(!atresetn)
    msg_cntr_ovf_d <= 1'b0;
  else if (atclken && (atb_syncrfr<8)) // periodic syncreq disabled
    msg_cntr_ovf_d <= 1'b0;
  else if (atclken)
    msg_cntr_ovf_d <= msg_cntr_ovf;
end

assign fsm_var = fsm;
always @ (posedge rtt_clk or negedge atresetn)
  begin : atb_fsm
    if(!atresetn) begin
        fsm     <= IDLE;
        rdata_r <= {(120-2*30){1'b1}};
        atdata  <= 64'b0;
        atvalid <= 1'b0;
        atbytes_msb <= 1'b0;
    end
    else if (has_rtt_iso_disable == 1'b0) begin
        fsm     <= IDLE;
        rdata_r <= {(120-2*30){1'b1}};
        atdata  <= 64'b0;
        atvalid <= 1'b0;
        atbytes_msb <= 1'b0;
    end
    else if (atclken) begin
        casez(fsm_var)
                IDLE : begin
                        if (!fifo_empty) begin
                          fsm     <= DO_1ST_PKT;                // process beat
                          rdata_r <= rdata_ns;                  // latch packets n:1
                          atdata  <= atdata_ns;                 // latch packet 0
                          atvalid <= 1'b1;                      // assert atvalid
                          atbytes_msb <= 1'b1;                  // set bytes to 4
                        end
                        else if(send_sync_req) begin
                          fsm     <= DO_SYNC_PKT;               // process syncreq
                          atdata  <= RTTSYNC_PACKET;            // latch frame packet
                          atvalid <= 1'b1;                      // assert atvalid
                          atbytes_msb <= 1'b0;                  // set bytes to 2
                        end
                end
                DO_SYNC_PKT : begin
                        if (atready) begin                      // wait for atdata ack
                          if (!fifo_empty) begin
                            fsm     <= DO_1ST_PKT;              // process beat
                            rdata_r <= rdata_ns;                // latch packets n:1
                            atdata  <= atdata_ns;               // latch packet 0
                            atvalid <= 1'b1;                    // assert atvalid
                            atbytes_msb <= 1'b1;                // set bytes to 4
                          end
                          else begin
                            atvalid <= 1'b0;                    // deassert atvalid
                            fsm     <= IDLE;                    // return to idle
                          end
                        end
                end
                DO_1ST_PKT : begin
                        if (atready) begin                      // wait for atdata ack
                          if (!last_packet) begin               // not the last packet.. keep processing packets
                            fsm     <= DO_NTH_PKT;              // Process next packet
                            rdata_r <= rdata_ns;                // shift to next packet
                            atdata  <= atdata_ns;               // latch packet 0
                          end
                          else if (send_sync_req) begin
                            fsm     <= DO_SYNC_PKT;             // process syncreq
                            atdata  <= RTTSYNC_PACKET;          // latch frame packet
                            atbytes_msb <= 1'b0;                // set bytes to 2
                          end
                          else if (fifo_empty) begin            // Single packet beat of last fifo data
                            fsm     <= IDLE;                    // return to idle
                            atvalid <= 1'b0;                    // deassert atvalid
                          end
                          else begin                            // Single packet beat, but fifo not empty so process next beat...
                            rdata_r <= rdata_ns;                // latch packets n:1
                            atdata  <= atdata_ns;               // latch packet 0
                          end
                        end
                end
                DO_NTH_PKT : begin
                        if (atready) begin                      // wait for atdata ack
                          if (!last_packet) begin               // not the last packet.. keep processing packets
                            atdata  <= atdata_ns;               // latch packet ...
                            rdata_r <= rdata_ns;                // shift to next packet
                          end
                          else if (send_sync_req) begin
                            fsm     <= DO_SYNC_PKT;             // process syncreq
                            atdata  <= RTTSYNC_PACKET;          // latch frame packet
                            atvalid <= 1'b1;                    // assert atvalid
                            atbytes_msb <= 1'b0;                // set bytes to 2
                          end
                          else if (fifo_empty) begin            // this is the last packet of last fifo data
                            fsm     <= IDLE;                    // return to idle
                            atvalid <= 1'b0;                    // deassert atvalid
                          end
                          else begin                            // This is the last packet of beat, but fifo not empty so process next beat...
                            fsm     <= DO_1ST_PKT;              // Process next beat
                            rdata_r <= rdata_ns;                // latch packets n:1
                            atdata  <= atdata_ns;               // latch packet 0
                          end
                        end
                end  
                default: fsm <= IDLE;
        endcase
    end
  end

always @ (posedge rtt_clk or posedge rst_a)
begin : PUSH_ALMOST_FULL_PIPELINE
  if(rst_a) begin
    push_af_pipe_d1 <= 1'b1;
  end
  else begin
    push_af_pipe_d1 <= ~push_af_pipe;
  end
end
assign fifo_full = push_af_pipe_d1;  //pipeline for timing, invert because we use this as an fifo_ack
assign nwr_en_qual = ~(wr_en & push_af_pipe_d1);

npuarc_rtt_atb_fifo #(.width(120),
                .depth(`npuarc_ATB_FIFO_DEPTH),
                .push_af_lvl(1)
                ) atb_trace_fifo (
        .rtt_clk(rtt_clk),
        .atclken(atclken),
        .rst_a(rst_a),
        .push_req_n(nwr_en_qual),
        .pop_req_n(~rd_req),
        .data_in(wr_data),
        .push_hf(push_hf),
        .push_af(push_af_pipe),
        .pop_empty(fifo_empty),
        .push_count(push_count),
        .pop_count(pop_count),
        .data_out(rdata)
        );

endmodule
