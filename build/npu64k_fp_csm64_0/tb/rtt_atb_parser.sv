// Library ARC RTT-2.10.3
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
//  atb_parser.sv 
//
// ===========================================================================
//
// Description:
//  input.txt -- memory file which has data to parse
//
//  coresight configuration
//  input.txt should have memory image of 64-bits / 32-bits in every line
//  if MEM_BUS_WIDTH=32, then input.txt should have data format as below
//  c0cef036
//  06fefa7a
//
//  change parameter values as per requirement
//  TIMESTAMP_EN     - should be set when timestamp register is programmed
//
// compilaton command:
//  vcs -sverilog -debug_acc+all atb_parser.sv -l compile.log
//
// simulation command:
//   ./simv -l sim.log
// ===========================================================================

`timescale 1ns / 1ns
`define HAS_ATB
//`define HAS_CTI_VAR_WIDTH
`define HAS_GRAD_ST
parameter TIMESTAMP_EN=0;
parameter NEXUS_DATA_WIDTH=8;
parameter MEM_BUS_WIDTH=32;
typedef enum bit {FALSE, TRUE} bool;


class nexus_transfer;
  bit [NEXUS_DATA_WIDTH-1:0]            msg_do[$];
  bit [7:0]            msg_seo[$];
  bit is_tstamp=TIMESTAMP_EN;
  `ifdef HAS_ATB
  bool is_src=FALSE;
  bit [5:0]            src=0;
  `else
  bool is_src=TRUE;
  bit [5:0]            src;
  `endif
  bit [5:0]            tcode;
  bit                  tstamp[];
  // OTM
  bit [7:0]            process_id;
// WTM
  bit                  wphit[];
// SWEM
  bit [3:0]            idtag;
  bit                  ext[];
  bit                  dqdata[];

// ERROR
  bit [11:0]            ecode;
  bit [3:0]             etype;
// PT-IBH
  bit                  hist[];
  bit                  uaddr[];
  bit                  icnt[];
  bit [1:0]            btype;
// PT - IBHS
  bit                  faddr[];
  bit                  dword_en;
// PT-RF
  bit                  rdata[];
  bit [3:0]            rcode;
// DT
  bit                  data[];
  bit [13:0]            rd_dcorr;
  bit [7:0]            wr_dcorr;
  bit [1:0]            dsz;
//SYNC  
  bit [4:0]            sync;
// PTCM
  bit                  cdata1[];
  bit                  cdata2[];
  bit [1:0]            cdf;
  bit [3:0]            evcode;
// DSM  
  bit [31:0]            status;
// CORE
  bit [5:0]            cr_addr;
  bit                  data2[];
//GRAD_ST
  bit 				commit_grad;
`ifdef RTT_USE_SYTIME
  bit   systimestamp[];
`endif
`ifdef HAS_ATB
`ifdef HAS_CTI_VAR_WIDTH
  bit			cstimestamp[];
`else
  bit [63:0]    cstimestamp;
`endif
`endif

  function void remove_zero (ref bit br[] );
    int unsigned i;
    bit dr[$];
    dr = {>>{br}};
    if (dr.size() > 1) begin
       for (i = dr.size()-1;i>0;i--) begin
         if (dr[i] != 0) break;
         else dr.delete(i);
       end
       br = {>>{dr}};
    end
  endfunction : remove_zero

  function void var_dis (ref bit br[],bit[1:0] exp);
    bit      sem[];
    bit[1:0] ctrl;
    bit[NEXUS_DATA_WIDTH-1:0] sotta;
    bit  lameh = 1'b0;

    br.delete();
    while(msg_do.size() > 0) begin
      ctrl = msg_seo.pop_front();
      sotta = msg_do.pop_front();
      sem = {<<{sotta}};
      br = {br,sem};
      if (ctrl == exp) begin 
        lameh = 1'b1;
        break;
      end
      else begin
        if (ctrl != 2'b00) begin
		  //$display("ERROR - Invalid seo field received!");
        end       
     end
    end

    if (lameh != 1'b1) begin
        //$display("ERROR - Invalid seo field during nexus transfer!");
    end
  endfunction : var_dis

  function bit [7:0] message_disassembler();
  	int unsigned msg_size;
  	bit [NEXUS_DATA_WIDTH-1:0]            tmp_msg_do[$];
  	bit [7:0]            tmp_msg_seo[$];
	bit[NEXUS_DATA_WIDTH-1:0] potta;
    bit [5:0] sotta;
    bit [7:0] tcode_out;
	bit      rem[];
    bit      dyn[];
	bit 	 tmp=1'b0;
    bit[1:0] ctrl;
  	tmp_msg_do = msg_do;
  	tmp_msg_seo = msg_seo;
  	msg_size = msg_do.size();
  	potta = msg_do[0];
  	if (NEXUS_DATA_WIDTH > 4) begin
  	  tcode = potta[5:0];
  	  ////$display(tcode);
  	end
  	else begin
  	  sotta = potta;
  	  sotta[5:4] = msg_do[1];
  	  tcode = sotta[5:0];
  	  ////$display(tcode);
  	end

	case (tcode)
        0     : begin
				//$display("------Message type is Debug status");
                   if (msg_do.size() > 1) ctrl=2'b11;
                   else ctrl=2'b10;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if(is_src == TRUE) begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,status,src,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,status,src,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                   else begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,status,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,status,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                  ////$display(tstamp);
                end
        2     : begin
				//$display("------Message type is Ownership trace");
                   if (msg_do.size() > 1) ctrl=2'b11;
                   else ctrl=2'b10;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if(is_src == TRUE) begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,process_id,src,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,process_id,src,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                   else begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,process_id,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,process_id,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                  ////$display(tstamp);
                end
        5   : begin
				//$display("------Message type is Data Trace write");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
				   `ifdef HAS_GRAD_ST
                   if (is_src == TRUE) {<<{uaddr,commit_grad,wr_dcorr,dsz,src,tcode}} = dyn;
                   else {<<{uaddr,commit_grad,wr_dcorr,dsz,tcode}} = dyn;
				   `else
                   if (is_src == TRUE) {<<{uaddr,wr_dcorr,dsz,src,tcode}} = dyn;
                   else {<<{uaddr,wr_dcorr,dsz,tcode}} = dyn;
			   	   `endif
                   uaddr = {<<{uaddr}};
                   remove_zero(uaddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(data,ctrl);
                   remove_zero(data);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(uaddr);
                  ////$display(data);
                  ////$display(tstamp);
                end
        6   : begin
				//$display("------Message type is Data Trace Read");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) {<<{uaddr,rd_dcorr,dsz,src,tcode}} = dyn;
                   else {<<{uaddr,rd_dcorr,dsz,tcode}} = dyn;
                   uaddr = {<<{uaddr}};
                   remove_zero(uaddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(data,ctrl);
                   remove_zero(data);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(data);
                  ////$display(tstamp);
                end
        7   : begin
				//$display("------Message type is SWEM");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) {<<{ext,idtag,src,tcode}} = dyn;
                   else {<<{ext,idtag,tcode}} = dyn;
                   ext = {<<{ext}};
                   remove_zero(ext);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(dqdata,ctrl);
                   remove_zero(dqdata);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  //$display(idtag);
                  //$display(ext);
                  //$display(dqdata);
                end                
        8     : begin
				//$display("------Message type is ERROR Message");
                   if (msg_do.size() > 1) ctrl=2'b11;
                   else ctrl=2'b10;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if(is_src == TRUE) begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,ecode,etype,src,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,ecode,etype,src,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                   else begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,ecode,etype,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,ecode,etype,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                  ////$display(tstamp);
                end
        9     : begin
				//$display("------Message type is PC-SYNC");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) {<<{icnt,sync,src,tcode}} = dyn;
                   else {<<{icnt,sync,tcode}} = dyn;
                   icnt = {<<{icnt}};
                   remove_zero(icnt);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(faddr,ctrl);
                   remove_zero(faddr);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(icnt);
                  ////$display(faddr);
                  ////$display(tstamp);
                end
        13    : begin
				//$display("------Message type is Data-Trace-Write-sync");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
				   `ifdef HAS_GRAD_ST
                   if (is_src == TRUE) {<<{faddr,commit_grad,wr_dcorr,dsz,sync,src,tcode}} = dyn;
                   else {<<{faddr,commit_grad,wr_dcorr,dsz,sync,tcode}} = dyn;
				   `else
                   if (is_src == TRUE) {<<{faddr,wr_dcorr,dsz,sync,src,tcode}} = dyn;
                   else {<<{faddr,wr_dcorr,dsz,sync,tcode}} = dyn;
			   	   `endif
                   faddr = {<<{faddr}};
                   remove_zero(faddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(data,ctrl);
                   remove_zero(data);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(faddr);
                  ////$display(data);
                  ////$display(tstamp);
                end
        14    : begin
				//$display("------Message type is Data-Trace-Read-sync");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   //$display(dyn);
                   if (is_src == TRUE) {<<{faddr,rd_dcorr,dsz,sync,src,tcode}} = dyn;
                   else {<<{faddr,rd_dcorr,dsz,sync,tcode}} = dyn;
                   faddr = {<<{faddr}};
                   remove_zero(faddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(data,ctrl);
                   remove_zero(data);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(faddr);
                  ////$display(data);
                  ////$display(tstamp);
                end
        15    : begin
				//$display("------Message type is Watchpoint");
                   if (is_tstamp == 1'b0) begin
                     if (msg_do.size() > 1) ctrl=2'b11;
                     else ctrl=2'b10;
                   end
                   else ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) {<<{wphit,src,tcode}} = dyn;
                   else {<<{wphit,tcode}} = dyn;
                   wphit = {<<{wphit}};
                   remove_zero(wphit);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(wphit);
                  ////$display(tstamp);
                end
        27    : begin
				//$display("------Message type is Resource-Full");
				`ifdef HAS_ATB
					potta = msg_do[0];
					rcode = potta[7:6]; 
					potta = msg_do[1];
					rcode = {potta[1:0],rcode[1:0]};
				`else
                   if (NEXUS_DATA_WIDTH == 8) begin
                     potta = msg_do[1];
                     rcode = potta[7:4];
                   end 
                   else if (NEXUS_DATA_WIDTH == 16) begin
                     potta = msg_do[0];
                     rcode = potta[15:12];
                   end
                   else begin
                     //potta = msg_do[2];
                     //sotta = msg_do[3];
                     //potta[2:0] = potta[3:1];
                     //potta[3:3] = sotta[0:0];
                     //rcode = potta;
					 rcode = msg_do[3];
                   end
				`endif
                   //if (is_tstamp == 1'b0 || rcode == 'b0) begin
                   if (is_tstamp == 1'b0 || rcode == 'b0 || rcode == 'h8) begin
                     if (msg_do.size() > 1) ctrl=2'b11;
                     else ctrl=2'b10;
                   end
                   else ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) begin
                     //if (rcode != 0 ) begin
                     if (rcode == 1 ) begin
                       {<<{rdata,rcode,src,tcode}} = dyn;
                       rdata = {<<{rdata}};
                       remove_zero(rdata);
                     end
                     else if (rcode == 2 ) begin
                       {<<{rdata,rcode,src,tcode}} = dyn;
                       rdata = {<<{rdata}};
                       remove_zero(rdata);
                     end
                     else begin //rcode is 0 or 8
                       if (is_tstamp == 1'b1) begin
                         {<<{tstamp,rcode,src,tcode}} = dyn;
                         tstamp = {<<{tstamp}};
                         remove_zero(tstamp);
                         tmp = 1'b1;
                       end 
                       else begin
                         {<<{rem,rcode,src,tcode}} = dyn;
                         remove_zero(rem);
                         if (rem.size() ==1) $display("ERROR - Invalid rfm!");
                       end
                     end
                   end
                   else begin
                     //if (rcode != 0) begin
                     if (rcode == 1) begin
                       {<<{rdata,rcode,tcode}} = dyn;
                       rdata = {<<{rdata}};
                       remove_zero(rdata);
                     end
                     else if (rcode == 2) begin
                       {<<{rdata,rcode,tcode}} = dyn;
                       rdata = {<<{rdata}};
                       remove_zero(rdata);
                     end
                     else begin
                       if (is_tstamp == 1'b1) begin
                         {<<{tstamp,rcode,tcode}} = dyn;
                         tstamp = {<<{tstamp}};
                         remove_zero(tstamp);
                         tmp = 1'b1;
                       end 
                       else begin
                         {<<{rem,rcode,tcode}} = dyn;
                         remove_zero(rem);
                         if (rem.size() ==1 && rem[0] == 1'b0);
                         else   begin
                              $display("ERROR - Invalid message!");
                         end
                       end 
                     end 
                   end
                   if (is_tstamp == 1'b1 && tmp == 1'b0) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  ////$display(rdata);
                  ////$display(tstamp);
                end
        28    : begin
				//$display("------Message type is Program-Indirect-Branch");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) {<<{icnt,btype,src,tcode}} = dyn;
                   else {<<{icnt,btype,tcode}} = dyn;
                   icnt = {<<{icnt}};
                   remove_zero(icnt);
                   var_dis(uaddr,ctrl);
                   remove_zero(uaddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(hist,ctrl);
                   remove_zero(hist);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  //$display(icnt);
                  //$display(uaddr);
                  //$display(hist);
                  //$display(tstamp);
                end
        29    : begin
				//$display("------Message type is Program-Indirect-Branc-Sync");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   //$display(dyn);
                   if (is_src == TRUE) {<<{icnt,btype,sync,src,tcode}} = dyn;
                   else {<<{icnt,btype,sync,tcode}} = dyn;
                   icnt = {<<{icnt}};
                   remove_zero(icnt);
                   var_dis(faddr,ctrl);
                   remove_zero(faddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(hist,ctrl);
                   remove_zero(hist);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  //$display(icnt);
                  //$display(faddr);
                  //$display(hist);
                  //$display(tstamp);
                end
        33    : begin
				//$display("------Message type is Program-trace-correlation");
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   //$display(dyn);
                   if (is_src == TRUE) {<<{icnt,cdf,evcode,src,tcode}} = dyn;
                   else {<<{icnt,cdf,evcode,tcode}} = dyn;
                   icnt = {<<{icnt}};
                   remove_zero(icnt);
                   var_dis(cdata1,ctrl);
                   remove_zero(cdata1);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(cdata2,ctrl);
                   remove_zero(cdata2);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  //$display(icnt);
                  //$display(cdata2);
                  //$display(cdata1);
                  //$display(tstamp);
                end
        56    : begin
                   if (NEXUS_DATA_WIDTH == 8) begin
                     potta = msg_do[2];
                     dword_en = potta[7:7];
                   end 
                   else if (NEXUS_DATA_WIDTH == 16) begin
                     potta = msg_do[1];
                     dword_en = potta[7:7];
                   end
                   else begin
                     potta = msg_do[5];
                     dword_en = potta[3:3];
                   end
                   if ((is_tstamp == 1'b0) && (dword_en==0) ) begin
                     if (msg_do.size() > 1) ctrl=2'b11;
                     else ctrl=2'b10;
                   end
                   else ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   ////$display(dyn);
                   if (is_src == TRUE) {<<{data,dword_en,cr_addr,wr_dcorr,src,tcode}} = dyn;
                   else {<<{data,dword_en,cr_addr,wr_dcorr,tcode}} = dyn;
                   data = {<<{data}};
                   remove_zero(data);
                   if (dword_en == 1 ) begin
                     if (is_tstamp == 1'b0) ctrl=2'b11;
                     var_dis(data2,ctrl);
                     remove_zero(data2);
                   end
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                     if (tstamp.size() > 8) begin
                              //$display("ERROR - Invalid message!");
                     end
                   end
                  ////$display(data);
                  ////$display(data2);
                  ////$display(tstamp);
                end
        57,58 : begin
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   //$display(dyn);
                   if (is_src == TRUE) {<<{uaddr,wr_dcorr,src,tcode}} = dyn;
                   else {<<{uaddr,wr_dcorr,tcode}} = dyn;
                   uaddr = {<<{uaddr}};
                   remove_zero(uaddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(data,ctrl);
                   remove_zero(data);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  //$display(uaddr);
                  //$display(data);
                  //$display(tstamp);
                end
        59,60 : begin
                   ctrl=2'b01;
                   var_dis(dyn,ctrl);
                   //$display(dyn);
                   if (is_src == TRUE) {<<{faddr,wr_dcorr,sync,src,tcode}} = dyn;
                   else {<<{faddr,wr_dcorr,sync,tcode}} = dyn;
                   faddr = {<<{faddr}};
                   remove_zero(faddr);
                   if (is_tstamp == 1'b0) ctrl=2'b11;
                   var_dis(data,ctrl);
                   remove_zero(data);
                   if (is_tstamp == 1'b1) begin
                     ctrl=2'b11;
                     var_dis(tstamp,ctrl);
                     remove_zero(tstamp);
                   end
                  //$display(faddr);
                  //$display(data);
                  //$display(tstamp);
                end
		`ifdef HAS_ATB
        61    : begin
				//$display("------Message type is cs-timestamp");
		          `ifdef HAS_CTI_VAR_WIDTH
				   if(is_tstamp == TRUE) begin
				   ctrl = 2'b01;
		           end else begin
		             if (msg_do.size() > 1) ctrl=2'b11;
                             else ctrl=2'b10;
		           end
				   
				   var_dis(dyn,ctrl);
				   if(is_src == TRUE) {<<{cstimestamp,src,tcode}} = dyn;
				   else {<<{cstimestamp,tcode}} = dyn;
				   cstimestamp = {<<{cstimestamp}};
				   remove_zero(cstimestamp);
				   if(is_tstamp == TRUE) begin
				   		ctrl = 2'b11;
						var_dis(tstamp,ctrl);
						remove_zero(tstamp);
				   end
				   `else
                   if (msg_do.size() > 1) ctrl=2'b11;
                   else ctrl=2'b10;
                   var_dis(dyn,ctrl);
                   if(is_src == TRUE) begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,cstimestamp,src,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,cstimestamp,src,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
                   else begin
                     if (is_tstamp == 1'b1) begin
                       {<<{tstamp,cstimestamp,tcode}} = dyn;
                       tstamp = {<<{tstamp}};
                       remove_zero(tstamp);
                     end
                     else begin
                       {<<{rem,cstimestamp,tcode}} = dyn;
                       remove_zero(rem);
                       if (rem.size() ==1 && rem[0] == 1'b0);
                       else   begin
                              //$display("ERROR - Invalid message!");
                       end
                     end
                   end
				 `endif
                  ////$display(tstamp);
                end
		`endif

		`ifdef RTT_USE_SYTIME
        61    : begin
				//$display("------Message type is system-timestamp");
                   if (is_tstamp == 1'b1) begin
                   ctrl=2'b01;
		           end else begin
		             if (msg_do.size() > 1) ctrl=2'b11;
                             else ctrl=2'b10;
		           end
                   var_dis(dyn,ctrl);
                   if (is_tstamp == 1'b1) begin
                       if(is_src == TRUE) begin
                         		{<<{systimestamp,src,tcode}} = dyn;
                         		systimestamp = {<<{systimestamp}};
                         		remove_zero(systimestamp);
		               end
		               else begin
                                 {<<{systimestamp,tcode}} = dyn;
                                 systimestamp = {<<{systimestamp}};
                                 remove_zero(systimestamp);
		               end
		               ctrl=2'b11;
                       var_dis(tstamp,ctrl);
                       remove_zero(tstamp);
		           end
		           else begin
                       if(is_src == TRUE) begin
                                 {<<{systimestamp,src,tcode}} = dyn;
                                 systimestamp = {<<{systimestamp}};
                                 remove_zero(systimestamp);
		               end
		               else begin
                                 {<<{systimestamp,tcode}} = dyn;
                                 systimestamp = {<<{systimestamp}};
                                 remove_zero(systimestamp);
		               end
		           end

                end
           `endif
		   default: begin
					//$display("ERROR - Invalid tcode");
		   			end
      endcase
      tcode_out = {2'b00,tcode}; 
  return tcode_out;
  endfunction
endclass

//TB top which reads memory file and parse data
task rtt_atb_parser(
//integer infile;
//reg clk;
input start_parsing,
input [MEM_BUS_WIDTH-1:0] data_in [39:0],
output reg [255:0] data_out
);
reg [MEM_BUS_WIDTH-1:0] din;
int data_cnt,prod_num,push_data,axi_msg_count,tstamp_en;
bit[NEXUS_DATA_WIDTH+1:0] atbq[$],tmp_data;
bit[29:0] valid_bytes_4;
nexus_transfer initial_trans;
bit [31:0] dtw_faddr,tmp_addr; 
bit [7:0] tstamp;
//initial begin
//  clk = 0;
//  initial_trans = new;
//end
//always #1 clk = ~clk;

begin
    if(start_parsing) begin
  //data_out   = 64'h0;
 //  wait(start_parsing);
  initial_trans = new;

	for(int unsigned j=0;j<40;j++)  
  begin //{
    din = data_in[j];
  	//$display("Input data read from file is %h",din);
	 for(int unsigned j=0;j<7;j++) 
		 valid_bytes_4[j]   = din[j+1];
	 for(int unsigned j=0;j<8;j++) 
		 valid_bytes_4[j+7] = din[8+j];
	 for(int unsigned j=0;j<7;j++) 
		 valid_bytes_4[j+15]   = din[16+j+1];
	 for(int unsigned j=0;j<8;j++) 
		 valid_bytes_4[j+22] = din[24+j];

        atbq = {<<(NEXUS_DATA_WIDTH+2){valid_bytes_4}};
	 while (atbq.size() > 0) begin //parsing is apllied only for valid_bytes=3
           tmp_data = atbq.pop_front();
           initial_trans.msg_do.push_back(tmp_data[NEXUS_DATA_WIDTH-1:0]);
           initial_trans.msg_seo.push_back(tmp_data[NEXUS_DATA_WIDTH+1:NEXUS_DATA_WIDTH]);
           if (tmp_data[NEXUS_DATA_WIDTH+1:NEXUS_DATA_WIDTH+1] == 1) begin
			   //this occurs for padding bits as 1 for last 64-bit data
		     if(initial_trans.msg_seo.size() == 'h1 && (initial_trans.msg_seo[0][1:0] != 'b10)) begin
			 	initial_trans=new();
			 end
			 else begin
             	axi_msg_count =axi_msg_count+1;
             	//$display("no of messages completed from atb",axi_msg_count); //
	         	tstamp_en = TIMESTAMP_EN;
	   	     	if(!tstamp_en) begin
             	    initial_trans.is_tstamp = 1'b0;
	   	     	end
             	data_out[(axi_msg_count-1)*8+:8] = initial_trans.message_disassembler();
	   	     	if(tstamp_en) begin
				tstamp=0;
				for (int i=0;i<initial_trans.tstamp.size();i++) tstamp[i] = initial_trans.tstamp[i];
				//$display("timestamp %h",tstamp);
	   	     	end
             	initial_trans=new();
			 end
           end
       end // while
  end //}
  //$display("Tcodes %h",data_out); //
	//#100 $finish;
    end
    else begin
  axi_msg_count = 0;   
  data_out   = 256'h0;
    end
end

//initial begin
//	$vcdpluson();
//	$vcdplusmemon();
//end

endtask

