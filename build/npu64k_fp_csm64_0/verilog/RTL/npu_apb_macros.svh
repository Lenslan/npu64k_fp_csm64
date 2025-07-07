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

`ifndef NPU_APB_MACROS_INCLUDED
`define NPU_APB_MACROS_INCLUDED


`define APBWIRES(APBAW,APBDW,APBPREF) \
logic              APBPREF``psel;     // apb select \
logic              APBPREF``penable;  // apb enable \
logic  [APBAW-1:2] APBPREF``paddr;    // apb address \
logic              APBPREF``pwrite;   // apb direction \
logic  [APBDW-1:0] APBPREF``pwdata;   // apb write data \
logic              APBPREF``pready;   // apb ready \
logic  [APBDW-1:0] APBPREF``prdata;   // apb read data \
logic              APBPREF``pslverr   // apb transfer failure \

`define APBWIRESN(CL,APBAW,APBDW,APBPREF) \
logic  [CL-1:0]            APBPREF``psel;     // apb select \
logic  [CL-1:0]            APBPREF``penable;  // apb enable \
logic  [CL-1:0][APBAW-1:2] APBPREF``paddr;    // apb address \
logic  [CL-1:0]            APBPREF``pwrite;   // apb direction \
logic  [CL-1:0][APBDW-1:0] APBPREF``pwdata;   // apb write data \
logic  [CL-1:0]            APBPREF``pready;   // apb ready \
logic  [CL-1:0][APBDW-1:0] APBPREF``prdata;   // apb read data \
logic  [CL-1:0]            APBPREF``pslverr   // apb transfer failure \

`define APBMST(APBAW,APBDW,APBPREF) \
output logic              APBPREF``psel,     // apb select \
output logic              APBPREF``penable,  // apb enable \
output logic  [APBAW-1:2] APBPREF``paddr,    // apb address \
output logic              APBPREF``pwrite,   // apb direction \
output logic  [APBDW-1:0] APBPREF``pwdata,   // apb write data \
input  logic              APBPREF``pready,   // apb ready \
input  logic  [APBDW-1:0] APBPREF``prdata,   // apb read data \
input  logic              APBPREF``pslverr   // apb transfer failure \

`define APBMSTN(CL,APBAW,APBDW,APBPREF) \
output logic  [CL-1:0]            APBPREF``psel,     // apb select \
output logic  [CL-1:0]            APBPREF``penable,  // apb enable \
output logic  [CL-1:0][APBAW-1:2] APBPREF``paddr,    // apb address \
output logic  [CL-1:0]            APBPREF``pwrite,   // apb direction \
output logic  [CL-1:0][APBDW-1:0] APBPREF``pwdata,   // apb write data \
input  logic  [CL-1:0]            APBPREF``pready,   // apb ready \
input  logic  [CL-1:0][APBDW-1:0] APBPREF``prdata,   // apb read data \
input  logic  [CL-1:0]            APBPREF``pslverr   // apb transfer failure \

`define APBSLV(APBAW,APBDW,APBPREF) \
input  logic              APBPREF``psel,     // apb select \
input  logic              APBPREF``penable,  // apb enable \
input  logic  [APBAW-1:2] APBPREF``paddr,    // apb address \
input  logic              APBPREF``pwrite,   // apb direction \
input  logic  [APBDW-1:0] APBPREF``pwdata,   // apb write data \
output logic              APBPREF``pready,   // apb ready \
output logic  [APBDW-1:0] APBPREF``prdata,   // apb read data \
output logic              APBPREF``pslverr   // apb transfer failure \

`define APBINST(APBPREF,APBWPREF) \
.APBPREF``psel    ( APBWPREF``psel    ), \
.APBPREF``penable ( APBWPREF``penable ), \
.APBPREF``paddr   ( APBWPREF``paddr   ), \
.APBPREF``pwrite  ( APBWPREF``pwrite  ), \
.APBPREF``pwdata  ( APBWPREF``pwdata  ), \
.APBPREF``pready  ( APBWPREF``pready  ), \
.APBPREF``prdata  ( APBWPREF``prdata  ), \
.APBPREF``pslverr ( APBWPREF``pslverr )  \

`define APBINSTM(CL,APBPREF,APBWPREF) \
.APBPREF``psel    ( APBWPREF``psel[CL]    ), \
.APBPREF``penable ( APBWPREF``penable[CL] ), \
.APBPREF``paddr   ( APBWPREF``paddr[CL]   ), \
.APBPREF``pwrite  ( APBWPREF``pwrite[CL]  ), \
.APBPREF``pwdata  ( APBWPREF``pwdata[CL]  ), \
.APBPREF``pready  ( APBWPREF``pready[CL]  ), \
.APBPREF``prdata  ( APBWPREF``prdata[CL]  ), \
.APBPREF``pslverr ( APBWPREF``pslverr[CL] )  \

`define APBASYNCWIRES(APBAW,APBDW,APBPREF) \
logic                  APBPREF``req_a;    // request \
logic                  APBPREF``ack_a;    // acknowledge \
logic  [APBAW+APBDW:0] APBPREF``pcmd;     // address+write+wdata \
logic  [APBDW:0]       APBPREF``presp     // read data+slverr \

`define APBASYNCINI(APBAW,APBDW,APBPREF) \
output logic                  APBPREF``req_a,    // request \
input  logic                  APBPREF``ack_a,    // acknowledge \
output logic  [APBAW+APBDW:0] APBPREF``pcmd,     // address+write+wdata \
input  logic  [APBDW:0]       APBPREF``presp     // read data+slverr \

`define APBASYNCTGT(APBAW,APBDW,APBPREF) \
input  logic                  APBPREF``req_a,    // request \
output logic                  APBPREF``ack_a,    // acknowledge \
input  logic  [APBAW+APBDW:0] APBPREF``pcmd,     // address+wdata+write \
output logic  [APBDW:0]       APBPREF``presp     // read data+slverr \

`define APBASYNCINST(APBPREF,APBWPREF) \
.APBPREF``req_a  ( APBWPREF``req_a ),  \
.APBPREF``ack_a  ( APBWPREF``ack_a ),  \
.APBPREF``pcmd   ( APBWPREF``pcmd  ),  \
.APBPREF``presp  ( APBWPREF``presp )   \

`endif
