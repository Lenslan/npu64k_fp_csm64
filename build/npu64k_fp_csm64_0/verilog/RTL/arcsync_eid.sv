/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

module arcsync_eid
#(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 32,
  parameter logic [3:0] EVENT_PULSE_HIGH = 4'd5,
  parameter logic [3:0] EVENT_PULSE_LOW  = 4'd5,
  parameter logic [31:0] CORE_NUM   = 32'd1,
  parameter NUM_IRQ_PER_CORE = 1,
  parameter NUM_EVT_PER_CORE = 1,
  parameter ADDR_EID_SEND_EVENT_0 = 32'h4000,
  parameter ADDR_EID_RAISE_IRQ_0  = 32'h4A00,
  parameter ADDR_EID_ACK_IRQ_0    = 32'h4C80
)
(
  input     logic       [CORE_NUM-1:0]      arcsync_core_exist,
  input     logic       [CORE_NUM-1:0]      arcsync_core_wr_enable,
  input     logic                           mmio_sel,   // select target register group, valid at the cycle when *en is high
  input     logic       [ADDR_WIDTH-1:0]    mmio_addr,  // register address, valid at the cycle when *en is high
  input     logic                           mmio_wen,   // write enable for register
  input     logic                           mmio_ren,   // read enable for register
  output    logic       [DATA_WIDTH-1:0]    mmio_rdata, // read data, valid at the cycle when ren is high
  input     logic       [DATA_WIDTH-1:0]    mmio_wdata, // write data, valid at the cycle when wen is high
  output    logic       [1:0]               mmio_resp,  // {err, ack} the response is received at the cycle when *en is high

  input     logic       [CORE_NUM-1:0]      sys_sleep,         // If true then processor is sleeping

  // IRQ and Event
  output    logic       [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0]      arcsync_core_irq,    // interrupt outputs,from c0_irq0_a to c(n-1)_irq0_a
  output    logic       [(CORE_NUM*NUM_EVT_PER_CORE)-1:0]      arcsync_core_event,  // pulse event output,from c0_event0_a to c(n-1)_event0_a
  // Clock, reset and configuration
  input     logic                 rst_a,      // Asynchronous reset, active high
  input     logic                 clk         // Clock
);

localparam             CORE_NUM_S = signed'(CORE_NUM);   //note:signed version for genvar type checking
///////////////////////////////////////////////////////////////////////////////
//                   local wires and regs  declaration                       //
///////////////////////////////////////////////////////////////////////////////

//{error,ack},rdata,active
//logic [CORE_NUM-1:0] err;
//logic [CORE_NUM-1:0] err_invalid_region;
//logic [CORE_NUM-1:0] ack;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] ack_irq;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] ack_event;
logic err_eid;
logic ack_eid;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] prd_cnt_enable;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] prd_cnt_rdy_clear;
//MMIO register
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0][15:0] EID_SEND_EVENT;     // Send an event pulse to the core or external   0x1000 +  28N 0x1000 + 32N -4     
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0][15:0] EID_RAISE_IRQ;      // Raise a level interrupt                       0x1000 +  44N 0x1000 + 48N -4
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0][15:0] EID_ACK_IRQ;        // Acknowledge a received interrupt              0x1000 +  48N 0x1000 + 52N -4

// for ral test purpose. Backdoor write and front-door read check
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0][DATA_WIDTH-1:0] EID_RAISE_IRQ_RDATA;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0][DATA_WIDTH-1:0] EID_SEND_EVENT_RDATA;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0][DATA_WIDTH-1:0] EID_ACK_IRQ_RDATA;

//Event and Interrupt Dispatch
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_raise_irq_wen;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_ack_irq_wen;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] eid_send_eve_wen;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_raise_irq_ren;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_ack_irq_ren;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] eid_send_eve_ren;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_raise_irq_valid;//indicates EID_RAISE_IRQ[i] has been writen
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_r;          //this is output register connect to irq line
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_en;         //enable signal of eid_irq_r
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_next;       //next value of eid_irq_r
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_set;        //generate irq
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_clear;      //pull down irq
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_ack;  //The interrupt line will be de-asserted after ARCSync gets the acknowledgment.
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] status_r;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_status_set;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_irq_status_clear;
logic [(CORE_NUM*NUM_IRQ_PER_CORE)-1:0] eid_ack_irq_valid;//indicates EID_ACK_IRQ[i] has been writen
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] eid_send_eve_valid;//indicates EID_SEND_EVENT[i] has been writen
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0][3:0] prd_cnt;          //event period counter
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] cnt_flag;        //indicates the value of prd_cnt is in high period 
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] eid_event_out_r;  //the output register  assigned to event line
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] eid_event_out_next;//the next state of eid_event_out_r
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] pending_ind_r;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] prd_cnt_counting;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] pending_ind_r_enable;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] ack_pending_eve_req;
logic [(CORE_NUM*NUM_EVT_PER_CORE)-1:0] ack_pending_eve_req_r;

logic [(CORE_NUM*NUM_IRQ_PER_CORE) -1:0] err_irq;
logic [(CORE_NUM*NUM_IRQ_PER_CORE) -1:0] err_irq_invalid_region;
logic [(CORE_NUM*NUM_EVT_PER_CORE) -1:0] err_event;
logic [(CORE_NUM*NUM_EVT_PER_CORE) -1:0] err_event_invalid_region;
logic [DATA_WIDTH-1:0] mmio_irq_rdata;
logic [DATA_WIDTH-1:0] mmio_event_rdata;

//Access MMIO
for (genvar i=0; i<(CORE_NUM_S*NUM_IRQ_PER_CORE); i++) // { 
begin

assign EID_RAISE_IRQ_RDATA[i]  = {16'b0,{EID_RAISE_IRQ[i] & {16{eid_raise_irq_ren[i]}}}};
assign EID_ACK_IRQ_RDATA[i]    = {31'b0,{(status_r[i] & eid_ack_irq_ren[i])}};
assign EID_SEND_EVENT_RDATA[i] = {31'b0,{(sys_sleep[i%CORE_NUM_S] & eid_send_eve_ren[i])}};

assign eid_raise_irq_ren[i]  = arcsync_core_exist[i%CORE_NUM] && mmio_sel && mmio_ren && (mmio_addr == (ADDR_EID_RAISE_IRQ_0 + 8*unsigned'(i/CORE_NUM)*CORE_NUM + 4*unsigned'(i%CORE_NUM)) )  ;
assign   eid_ack_irq_ren[i]  = arcsync_core_exist[i%CORE_NUM] && mmio_sel && mmio_ren && (mmio_addr == (ADDR_EID_ACK_IRQ_0   + 8*unsigned'(i/CORE_NUM)*CORE_NUM + 4*unsigned'(i%CORE_NUM)) )  ; 
assign eid_raise_irq_wen[i]  = arcsync_core_wr_enable[i%CORE_NUM] && mmio_sel && mmio_wen && (mmio_addr == (ADDR_EID_RAISE_IRQ_0 + 8*unsigned'(i/CORE_NUM)*CORE_NUM + 4*unsigned'(i%CORE_NUM)) )  ;
assign   eid_ack_irq_wen[i]  = arcsync_core_wr_enable[i%CORE_NUM] && mmio_sel && mmio_wen && (mmio_addr == (ADDR_EID_ACK_IRQ_0   + 8*unsigned'(i/CORE_NUM)*CORE_NUM + 4*unsigned'(i%CORE_NUM)) )  ;

///////////////////////////////////////////////////////////////////////////////
//          Generating interrupts and acknowledge interrupts                 //
/////////////////////////////////////////////////////////////////////////////// 

//Write EID_RAISE_IRQ,the reset value is 32'hffffffff
  always @(posedge clk or posedge rst_a)
  begin:eid_raise_irq_r_PROC
    if (rst_a) 
      EID_RAISE_IRQ[i] <= 16'hffff;
    else if (eid_raise_irq_wen[i]
             & ~status_r[i])
      //~status_r is to ensure that no interrupt is overridden
      //It’s handled here instead of being handled in generating level irq,so that the right initiator core_id can be read.
// spyglass disable_block FlopEConst
// Enable pin EN on Flop is  always disabled (tied low). It depends on arcsync_core_exist[i%CORE_NUM] valud.
      EID_RAISE_IRQ[i] <= mmio_wdata[15:0];
// spyglass enable_block FlopEConst
  end:eid_raise_irq_r_PROC

  always @(posedge clk or posedge rst_a)
  begin:eid_raise_irq_valid_PROC
    if(rst_a) 
      eid_raise_irq_valid[i] <= 1'b0;
    else if (eid_raise_irq_wen[i]
             & ~status_r[i])
      eid_raise_irq_valid[i] <= 1'b1;
    else
      eid_raise_irq_valid[i] <= 1'b0;
  end:eid_raise_irq_valid_PROC

///////////////////////////////////////////////////////////////////////////////////////////////////////////
//generate interrupt
//If the mmio value is no less than total number of cores in system, 
//then the interrupt was triggered by external system.
//
assign eid_irq_set[i]=eid_raise_irq_valid[i]//according to MMIO register been writen
                   & (~(EID_RAISE_IRQ[i] == 16'hffff)) //if rst value not generate irq
                   ;             

assign eid_irq_clear[i] = eid_irq_ack[i];  

////////////////////////////////////////////////////////////////////////////////////////////////////////////
//if the set and clear condition to be true at the same time ,the higher priority should be the set condition. 
//At this case, the bit will be asserted to indicate a new interrupt.
//
assign eid_irq_en[i]    = eid_irq_set[i] | eid_irq_clear[i];
assign eid_irq_next[i]  = eid_irq_set[i] | (~eid_irq_clear[i]);


always@(posedge clk or posedge rst_a)
  begin:eid_irq_r_PROC
    if(rst_a)
      eid_irq_r[i] <= 1'b0;
    else if(eid_irq_en[i] == 1'b1)
      eid_irq_r[i] <= eid_irq_next[i];
  end:eid_irq_r_PROC

//output irq
assign arcsync_core_irq[i] = eid_irq_r[i];

//Write EID_ACK_IRQ, the reset value is 32'hffffffff
 always @(posedge clk or posedge rst_a)
  begin:eid_ack_irq_r_PROC
    if(rst_a) 
      EID_ACK_IRQ[i] <= 16'hffff;
    else if (eid_ack_irq_wen[i])
      EID_ACK_IRQ[i] <= mmio_wdata[15:0];
  end:eid_ack_irq_r_PROC

  always @(posedge clk or posedge rst_a)
  begin:eid_ack_irq_valid_PROC
    if(rst_a) 
      eid_ack_irq_valid[i] <= 1'b0;
    else if (eid_ack_irq_wen[i])
      eid_ack_irq_valid[i] <= 1'b1;
    else
      eid_ack_irq_valid[i] <= 1'b0;
  end:eid_ack_irq_valid_PROC

//internal status register
//if initiator core not writeing the default value to raise an interrupt, status_r turns to 1'b1 
//if receiving core writes its own core ID to ack the IRQ, the status_r cleared to zero
assign eid_irq_status_set[i] = eid_raise_irq_wen[i] & ~status_r[i] & ~(mmio_wdata == 32'hffffffff) ;
assign eid_irq_status_clear[i] = eid_ack_irq_wen[i] & (mmio_wdata==(i%CORE_NUM));

 always @(posedge clk or posedge rst_a)
  begin:eid_status_r_PROC
    if(rst_a) 
      status_r[i] <= 1'b0;
    else if (eid_irq_status_set[i])
      status_r[i] <= 1'b1;
    else if (eid_irq_status_clear[i])
      status_r[i] <= 1'b0;
  end:eid_status_r_PROC

//acknowlege pulse 
assign eid_irq_ack[i] = eid_ack_irq_valid[i] & (EID_ACK_IRQ[i] == (i%CORE_NUM));


//if requests is to those registers which do not existed with undefined core index or undefined address, return error;
//the value writen to EID_ACK_IRQ is not his self core_id return error
//write to EID_RAISE_IRQ when there is pending irq just ignore, |(eid_raise_irq_wen[i] & status_r[i])
//write self core_id to EID_RAISE_IRQ, it make sense to make irq to itself, eg:test irq line;

assign err_irq[i] = (eid_ack_irq_wen[i] && mmio_wdata != (i%CORE_NUM));

assign err_irq_invalid_region[i] = (arcsync_core_exist[i%CORE_NUM] & mmio_sel & mmio_ren) & ~(eid_raise_irq_ren[i] | eid_ack_irq_ren[i] )
                                   | (!arcsync_core_exist[i%CORE_NUM] & mmio_sel & mmio_ren)
                                   | (arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen & ~(eid_raise_irq_wen[i] | eid_ack_irq_wen[i]))
                                   | (!arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen)
                                   |(1'b0);

//ack indicates the module acknowledge the request
//write to EID_RAISE_IRQ when there is pending irq just ignore, response ack

assign ack_irq[i] = (arcsync_core_exist[i%CORE_NUM] & mmio_sel & mmio_ren)
                   |(arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen & eid_raise_irq_wen[i])
                   |(arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen & eid_ack_irq_wen[i]  )
                   |(1'b0) ;


end // } CORE_NUM_S*NUM_IRQ_PER_CORE LOOP


  always_comb
  begin:irq_read_data_PROC
    mmio_irq_rdata =32'b0;
    for (int unsigned i=0; i<(CORE_NUM_S*NUM_IRQ_PER_CORE); i++) // { 
    begin
      if(mmio_sel)
      begin
      if(eid_raise_irq_wen[i] | eid_ack_irq_wen[i])
        begin
         mmio_irq_rdata = 32'b0;
        end
      else if(eid_raise_irq_ren[i]) 
        begin  
        //read EID_RAISE_IRQ return the initiator core_id
        //mmio_irq_rdata = {16'b0,{EID_RAISE_IRQ[i] & {16{eid_raise_irq_ren[i]}}}} ;
        mmio_irq_rdata = EID_RAISE_IRQ_RDATA[i]; // for ral test pupose: backdoor write and front-door read check
        end
      else if(eid_ack_irq_ren[i])
        begin  
        //read EID_ACK_IRQ return the value of status_r
        //mmio_irq_rdata = {31'b0,{(status_r[i] & eid_ack_irq_ren[i])}};
        mmio_irq_rdata = EID_ACK_IRQ_RDATA[i]; // for ral test pupose: backdoor write and front-door read check
        end
      end
    end
  end


for (genvar i=0; i<(CORE_NUM_S*NUM_EVT_PER_CORE); i++) // { 
  begin
///////////////////////////////////////////////////////////////////////////////
//                  Generating Events and Check Event Status                 //
///////////////////////////////////////////////////////////////////////////////

assign  eid_send_eve_ren[i]  = arcsync_core_exist[i%CORE_NUM] && mmio_sel && mmio_ren && (mmio_addr == (ADDR_EID_SEND_EVENT_0 + 4*unsigned'(i/CORE_NUM)*CORE_NUM + 4*unsigned'(i%CORE_NUM) ) )  ;
assign  eid_send_eve_wen[i]  = arcsync_core_wr_enable[i%CORE_NUM] && mmio_sel && mmio_wen && (mmio_addr == (ADDR_EID_SEND_EVENT_0 + 4*unsigned'(i/CORE_NUM)*CORE_NUM + 4*unsigned'(i%CORE_NUM) ) )  ;

 always @(posedge clk or posedge rst_a)
  begin:eid_send_eve_r_PROC
    if(rst_a) 
      EID_SEND_EVENT[i] <= 16'b0;
//if the period counter count to 10, it will trun to 0
    else if(prd_cnt_rdy_clear[i])                                                                               
      EID_SEND_EVENT[i] <= 16'b0;
    else if (eid_send_eve_wen[i] & ~(|prd_cnt[i]) & ~eid_send_eve_valid[i]) 
      EID_SEND_EVENT[i] <= {15'b0,mmio_wdata[0]};
  end:eid_send_eve_r_PROC

//valid signal indicates whether the register has been writen 1 or 0, is the pulse signal,only one cycle, 
//valid change to 1 only when its value is 0, to get rid of valid stay high for two cycles
  always @(posedge clk or posedge rst_a)
  begin:eid_send_eve_valid_PROC
    if(rst_a) 
      eid_send_eve_valid[i] <= 1'b0;
    else if ((eid_send_eve_wen[i] & ~(|prd_cnt[i]) & ~eid_send_eve_valid[i]) || ack_pending_eve_req[i] )
      eid_send_eve_valid[i] <= 1'b1;
    else 
      eid_send_eve_valid[i] <= 1'b0;
  end:eid_send_eve_valid_PROC

//pending_ind_r indicates that there is a pneding reques need to ack
//writen request comes when valid pulled up or counting from 1 to 9,the indicate reg will be pull up
//
  always @(posedge clk or posedge rst_a)
  begin:pending_ind_r_PROC
    if(rst_a) 
      pending_ind_r[i] <= 1'b0;
    else if ( pending_ind_r_enable[i]  )
      pending_ind_r[i] <= 1'b1;
    else if (prd_cnt_rdy_clear[i]) 
      pending_ind_r[i] <= 1'b0;
  end:pending_ind_r_PROC

assign prd_cnt_counting[i] = (prd_cnt[i] < (EVENT_PULSE_HIGH + EVENT_PULSE_LOW)) && (prd_cnt[i] > 4'd0);
assign pending_ind_r_enable[i] = eid_send_eve_wen[i] & (prd_cnt_counting[i] || eid_send_eve_valid[i]);

//this signal indicates the pulse of responding the pending request, at the last cycle of event
assign ack_pending_eve_req[i] = (pending_ind_r[i] || eid_send_eve_wen[i]) & prd_cnt_rdy_clear[i] ;

  always @(posedge clk or posedge rst_a)
  begin:ack_pending_eve_req_r_PROC
    if(rst_a) 
      ack_pending_eve_req_r[i] <= 1'b0;
    else 
      ack_pending_eve_req_r[i] <= ack_pending_eve_req[i];
  end:ack_pending_eve_req_r_PROC
//////////////////////////////////////////////////////////////////////////////////////////////////////
//prd_cnt count from 1 to 10
//
assign prd_cnt_enable[i] = (eid_send_eve_valid[i] & (|EID_SEND_EVENT[i])) 
                           || (eid_send_eve_valid[i] & (|ack_pending_eve_req_r[i])) 
                           || (prd_cnt_counting[i]);

assign prd_cnt_rdy_clear[i] = (prd_cnt[i] == (EVENT_PULSE_HIGH + EVENT_PULSE_LOW)) ;

//event period counter
  always @(posedge clk or posedge rst_a)
  begin:prd_cnt_r_PROC
    if(rst_a) 
      prd_cnt[i] <= 4'd0;
    else if (prd_cnt_enable[i])    
      prd_cnt[i] <= prd_cnt[i] + 4'd1 ;
    else
      prd_cnt[i] <= 4'd0;                                           
  end:prd_cnt_r_PROC

assign cnt_flag[i] = ((prd_cnt[i] < (EVENT_PULSE_HIGH +4'd1)) && (prd_cnt[i] > 4'd0))
                 & ~((prd_cnt[i] < EVENT_PULSE_HIGH + EVENT_PULSE_LOW +1) && (prd_cnt[i] > EVENT_PULSE_HIGH))    
                 | 1'b0 ;

assign eid_event_out_next[i] = cnt_flag[i] ;

//generate event pulse
  always @(posedge clk or posedge rst_a)
  begin:eve_out_PROC
    if(rst_a)
      eid_event_out_r[i] <= 1'b0;
    else
      eid_event_out_r[i] <= eid_event_out_next[i];        
  end:eve_out_PROC

//output event
assign arcsync_core_event[i] = eid_event_out_r[i];

assign err_event[i] = 1'b0;

assign err_event_invalid_region[i] = (arcsync_core_exist[i%CORE_NUM] & mmio_sel & mmio_ren) & ~(eid_send_eve_ren[i])
                                     | (!arcsync_core_exist[i%CORE_NUM] & mmio_sel & mmio_ren)
                                     | (arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen) & ~(eid_send_eve_wen[i])
                                     | (!arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen)
                                     | (1'b0);

//ack indicates the module acknowledge the request
//writing to EID_SEND_EVENT if there is pending event pulse generating,the request stalls.
//if the write request comes when there is pending event, 
//the ack will response at the cycle when the prd_cnt count to 10, and no error response.
assign ack_event[i] = (arcsync_core_exist[i%CORE_NUM] & mmio_sel & mmio_ren)
                     |(arcsync_core_wr_enable[i%CORE_NUM] & mmio_sel & mmio_wen & eid_send_eve_wen[i] & ~(|prd_cnt[i]) & ~eid_send_eve_valid[i])
                     |(pending_ind_r[i] || eid_send_eve_wen[i]) & prd_cnt_rdy_clear[i]
                     |(1'b0) ;


end // } CORE_NUM_S*NUM_EVT_PER_CORE LOOP



always_comb
begin:event_read_data_PROC
  mmio_event_rdata =32'b0;
  if(mmio_sel)
  begin
    for (int unsigned i=0; i<(CORE_NUM_S*NUM_EVT_PER_CORE); i++) // { 
    begin
      if(eid_send_eve_ren[i])
      begin
        //mmio_event_rdata = {31'b0,{(sys_sleep[i%CORE_NUM_S] & eid_send_eve_ren[i])}} ;
        mmio_event_rdata = EID_SEND_EVENT_RDATA[i]; // for ral test pupose: backdoor write and front-door read check
      end
    end
  end
end

///////////////////////////////////////////////////////////////////////////////
//          Output mmio_rdata     return{error,ack}                          //
///////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////
//                      mmio_resp                    //
///////////////////////////////////////////////////////                

assign err_eid = (|err_irq) | (|err_event) | ((&err_irq_invalid_region) & (&err_event_invalid_region));

assign ack_eid = (|ack_irq) | (|ack_event) | ((&err_irq_invalid_region) & (&err_event_invalid_region));
assign mmio_resp = {err_eid,ack_eid} ; 

///////////////////////////////////////////////////////
//////////////////// return read data /////////////////
///////////////////////////////////////////////////////
always_comb
begin:read_data_PROC
  mmio_rdata =32'b0;
for (int unsigned i=0;i<CORE_NUM;i++)
  begin
    if(mmio_sel)
    begin
    if(eid_raise_irq_wen[i] | eid_ack_irq_wen[i] | eid_send_eve_wen[i])
      begin
       mmio_rdata = 32'b0;
      end
    else if((|eid_raise_irq_ren) | (|eid_ack_irq_ren)) 
      begin  
      mmio_rdata = mmio_irq_rdata;
      end
    else if(|eid_send_eve_ren)
      begin
      mmio_rdata = mmio_event_rdata;
      end
    end
  end
end
/////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////
// Properties
/////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////
`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_eid.sv"
`endif
endmodule
