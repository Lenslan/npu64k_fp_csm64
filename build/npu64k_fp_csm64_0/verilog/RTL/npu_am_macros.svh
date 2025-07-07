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

//
// File defining macros for a parameterizable AM interface
// Parameters to control the instantiation
// - AMPREF:   prefix of the AM interface
// - AMWPREF:  prefix of the wires connected to an AM interface instance (AMINST)
//
// Here is an example of how to use these macros:
//
//import npu_types::*;
//
//`include "npu_am_macros.svh"
//
//// create a module with an AM master and slave interface
//module t(
//         `AMRMST(amm_),        // two AM master lanes read-only
//         `AMWSLV(ams_),        // three AM slave lanes write-only
//         input logic clk
//         );
//endmodule : t
//
//// create a module instantiating two AM interfaces and connecting to a submodule
//module top();
//    logic clk;
//    `AMRWIRES(ami_);
//    `AMWWIRES(vsi_);
//
//    t inst(
//           `AMRINST(amm_,ami_),
//           `AMWINST(ams_,vsi_),
//           .clk(clk)
//           );
//endmodule : top
//

`ifndef NPU_AM_MACROS_INCLUDED
`define NPU_AM_MACROS_INCLUDED

//
// NPU AM read-only wire declaration
//
`define AMRWIRES(AMPREF, N) \
// command channel \
logic     [N-1:0]     AMPREF``cmd_valid;  // read command valid \
logic     [N-1:0]     AMPREF``cmd_accept; // read command accept \
am_addr_t [N-1:0]     AMPREF``cmd_addr;   // read command address \
// read data channel \
logic     [N-1:0]     AMPREF``rvalid;     // read data valid \
vyixacc_t [N-1:0]     AMPREF``rdata       // read data \


//
// NPU AM read-only instance port list
//
// Batch port
`define AMRINST_B(AMPREF,AMWPREF) \
// read command channel \
.AMPREF``cmd_valid  ( AMWPREF``cmd_valid  ),  // read command valid \
.AMPREF``cmd_accept ( AMWPREF``cmd_accept ),  // read command accept \
.AMPREF``cmd_addr   ( AMWPREF``cmd_addr   ),  // read command address \
// read data channel \
.AMPREF``rvalid     ( AMWPREF``rvalid     ),  // read data valid \
.AMPREF``rdata      ( AMWPREF``rdata      )   // read data \

// Single port
`define AMRINST_S(AMPREF,AMWPREF, N) \
// read command channel \
.AMPREF``cmd_valid  ( AMWPREF``cmd_valid[N]  ),  // read command valid \
.AMPREF``cmd_accept ( AMWPREF``cmd_accept[N] ),  // read command accept \
.AMPREF``cmd_addr   ( AMWPREF``cmd_addr[N]   ),  // read command address \
// read data channel \
.AMPREF``rvalid     ( AMWPREF``rvalid[N]     ),  // read data valid \
.AMPREF``rdata      ( AMWPREF``rdata[N]      )   // read data \

// Tie single port
`define AMRTIE_S(AMPREF,AMWPREF, N) \
// read command channel \
assign AMWPREF``cmd_valid[N] = 1'b0;  // read command valid \
assign AMWPREF``cmd_addr[N]  = '0;   // read command address \

//
// NPU AM read-only module master port list
//
`define AMRMST(AMPREF, N) \
// command channel \
output logic     [N-1:0]     AMPREF``cmd_valid,  // read command valid \
input  logic     [N-1:0]     AMPREF``cmd_accept, // read command accept \
output am_addr_t [N-1:0]     AMPREF``cmd_addr,   // read command address \
// read data channel \
input  logic     [N-1:0]     AMPREF``rvalid,     // read data valid \
input  vyixacc_t [N-1:0]     AMPREF``rdata       // read data \


//
// NPU AM read-only module slave port list
//
`define AMRSLV(AMPREF, N) \
// command channel \
input  logic     [N-1:0]     AMPREF``cmd_valid,  // read command valid \
output logic     [N-1:0]     AMPREF``cmd_accept, // read command accept \
input  am_addr_t [N-1:0]     AMPREF``cmd_addr,   // read command address \
// read data channel \
output logic     [N-1:0]     AMPREF``rvalid,     // read data valid \
output vyixacc_t [N-1:0]     AMPREF``rdata       // read data \
                 

//
// NPU AM write-only wire declaration
//
`define AMWWIRES(AMPREF, N) \
// command channel \
logic     [N-1:0]     AMPREF``cmd_valid;   // write command valid \
logic     [N-1:0]     AMPREF``cmd_accept;  // write command accept \
am_addr_t [N-1:0]     AMPREF``cmd_addr;    // write command address \
// write data channel \
vyixacc_t [N-1:0]     AMPREF``wdata;       // write data \
logic     [N-1:0]     AMPREF``aw_consumed  // write consmed from fifo/skid
          
`define AMWWIRES_MSK(AMPREF, N) \
// command channel \
logic     [N-1:0]     AMPREF``cmd_valid;  // write command valid \
logic     [N-1:0]     AMPREF``cmd_accept; // write command accept \
am_addr_t [N-1:0]     AMPREF``cmd_addr;   // write command address \
// write data channel \
vyixacc_t [N-1:0]     AMPREF``wdata;       // write data \
ixambit_t [N-1:0]     AMPREF``wstrb       // write data \

//
// NPU AM write-only instance port list
//
// Batch port
`define AMWINST_B(AMPREF,AMWPREF) \
// write command channel \
.AMPREF``cmd_valid   ( AMWPREF``cmd_valid   ),  // write command valid \
.AMPREF``cmd_accept  ( AMWPREF``cmd_accept  ),  // write command accept \
.AMPREF``cmd_addr    ( AMWPREF``cmd_addr    ),  // write command address \
// write data channel \
.AMPREF``wdata       ( AMWPREF``wdata       ),   // write data \
.AMPREF``aw_consumed ( AMWPREF``aw_consumed )  // write consumed from fifo/skid

`define AMWINST_B_MSK(AMPREF,AMWPREF) \
// write command channel \
.AMPREF``cmd_valid  ( AMWPREF``cmd_valid  ),  // write command valid \
.AMPREF``cmd_accept ( AMWPREF``cmd_accept ),  // write command accept \
.AMPREF``cmd_addr   ( AMWPREF``cmd_addr   ),  // write command address \
// write data channel \
.AMPREF``wdata      ( AMWPREF``wdata      ),   // write data \
.AMPREF``wstrb      ( AMWPREF``wstrb      )   // write data \

// Single port
`define AMWINST_S(AMPREF,AMWPREF, N) \
// write command channel \
.AMPREF``cmd_valid   ( AMWPREF``cmd_valid[N]   ),  // write command valid \
.AMPREF``cmd_accept  ( AMWPREF``cmd_accept[N]  ),  // write command accept \
.AMPREF``cmd_addr    ( AMWPREF``cmd_addr[N]    ),  // write command address \
// write data channel \
.AMPREF``wdata       ( AMWPREF``wdata[N]       ),   // write data \
.AMPREF``aw_consumed ( AMWPREF``aw_consumed[N] )  // write consumed from fifo/skid \

// Tie a single port
`define AMWTIE_S(AMPREF,AMWPREF, N) \
// write command channel \
assign AMWPREF``cmd_valid[N] = 1'b0; // write command valid \
assign AMWPREF``cmd_addr[N]  = '0;   // write command address \
// write data channel \
assign AMWPREF``wdata[N]     = '0;   // write data \


//
// NPU AM write-only module master port list
//
`define AMWMST(AMPREF, N) \
// command channel \
output logic     [N-1:0]     AMPREF``cmd_valid,  // write command valid \
input  logic     [N-1:0]     AMPREF``cmd_accept, // write command accept \
output am_addr_t [N-1:0]     AMPREF``cmd_addr,   // write command address \
// write data channel \
output vyixacc_t [N-1:0]     AMPREF``wdata,      // write data \
input  logic     [N-1:0]     AMPREF``aw_consumed // write consumed from fifo/skid 

`define AMWMST_MSK(AMPREF, N) \
// command channel \
output logic     [N-1:0]     AMPREF``cmd_valid,  // write command valid \
input  logic     [N-1:0]     AMPREF``cmd_accept, // write command accept \
output am_addr_t [N-1:0]     AMPREF``cmd_addr,   // write command address \
// write data channel \
output vyixacc_t [N-1:0]     AMPREF``wdata,      // write data \
output ixambit_t [N-1:0]     AMPREF``wstrb       // write data \

//
// NPU AM write-only module slave port list
//
`define AMWSLV(AMPREF, N) \
// command channel \
input  logic     [N-1:0]     AMPREF``cmd_valid,  // write command valid \
output logic     [N-1:0]     AMPREF``cmd_accept, // write command accept \
input  am_addr_t [N-1:0]     AMPREF``cmd_addr,   // write command address \
// write data channel \
input  vyixacc_t [N-1:0]     AMPREF``wdata,       // write data \
output logic     [N-1:0]     AMPREF``aw_consumed  // write command consumed from write fifo or skid \

`define AMWSLV_MSK(AMPREF, N) \
// command channel \
input  logic     [N-1:0]     AMPREF``cmd_valid,  // write command valid \
output logic     [N-1:0]     AMPREF``cmd_accept, // write command accept \
input  am_addr_t [N-1:0]     AMPREF``cmd_addr,   // write command address \
// write data channel \
input  vyixacc_t [N-1:0]     AMPREF``wdata,      // write data \
input  ixambit_t [N-1:0]     AMPREF``wstrb       // write data \

`define AMMST(AMLANES,AMPREF) \
output logic          [AMLANES-1:0] AMPREF``mem_en,  // load enable \
output logic          [AMLANES-1:0] AMPREF``ls,      // light sleep \
output logic          [AMLANES-1:0] AMPREF``ds,      // deep sleep \
output logic          [AMLANES-1:0] AMPREF``ldst_en, // store enable\
output am_addr_t      [AMLANES-1:0] AMPREF``addr,    // command address \
output vyixacc_t      [AMLANES-1:0] AMPREF``wdata,   // write data \
input  vyixacc_t      [AMLANES-1:0] AMPREF``rdata    // read data \

`define AMMST_MSK(AMLANES,AMPREF) \
output logic          [AMLANES-1:0] AMPREF``mem_en,  // load enable \
output logic          [AMLANES-1:0] AMPREF``ls,      // light sleep \
output logic          [AMLANES-1:0] AMPREF``ds,      // deep sleep \
output logic          [AMLANES-1:0] AMPREF``ldst_en, // store enable\
output am_addr_t      [AMLANES-1:0] AMPREF``addr,    // command address \
output vyixacc_t      [AMLANES-1:0] AMPREF``wdata,   // write data \
output ixambit_t      [AMLANES-1:0] AMPREF``wstrb,   // write strobe\
input  vyixacc_t      [AMLANES-1:0] AMPREF``rdata    // read data

//
// NPU am memory module master port list
//
`define AMSLV(AMLANES,AMPREF) \
input  logic          [AMLANES-1:0] AMPREF``mem_en,  // load enable\
input  logic          [AMLANES-1:0] AMPREF``ls,      // light sleep \
input  logic          [AMLANES-1:0] AMPREF``ds,      // deep sleep \
input  logic          [AMLANES-1:0] AMPREF``ldst_en, // store enable\
input  am_addr_t      [AMLANES-1:0] AMPREF``addr,    // command address \
input  vyixacc_t      [AMLANES-1:0] AMPREF``wdata,   // write data \
output vyixacc_t      [AMLANES-1:0] AMPREF``rdata    // read data \

`define AMSLV_MSK(AMLANES,AMPREF) \
input  logic          [AMLANES-1:0] AMPREF``mem_en,  // load enable\
input  logic          [AMLANES-1:0] AMPREF``ls,      // light sleep \
input  logic          [AMLANES-1:0] AMPREF``ds,      // deep sleep \
input  logic          [AMLANES-1:0] AMPREF``ldst_en, // store enable\
input  am_addr_t      [AMLANES-1:0] AMPREF``addr,    // command address \
input  vyixacc_t      [AMLANES-1:0] AMPREF``wdata,   // write data \
input  ixambit_t      [AMLANES-1:0] AMPREF``wstrb,   // write data \
output vyixacc_t      [AMLANES-1:0] AMPREF``rdata    // read data \

//
// NPU AM memory instance port list
//
`define AMINST(AMLANES,AMPREF) \
.AMPREF``mem_en      ( AMPREF``mem_en     ),  // load enable \
.AMPREF``ls          ( AMPREF``ls         ),  // light sleep \
.AMPREF``ds          ( AMPREF``ds         ),  // deep sleep \
.AMPREF``ldst_en     ( AMPREF``ldst_en    ),  // store enable \
.AMPREF``addr        ( AMPREF``addr       ),  // address \
.AMPREF``wdata       ( AMPREF``wdata      ),  // write data \
.AMPREF``rdata       ( AMPREF``rdata      )   // read data \

`define AMINST_MSK(AMLANES,AMPREF) \
.AMPREF``mem_en      ( AMPREF``mem_en     ),  // load enable \
.AMPREF``ls          ( AMPREF``ls         ),  // light sleep \
.AMPREF``ds          ( AMPREF``ds         ),  // deep sleep \
.AMPREF``ldst_en     ( AMPREF``ldst_en    ),  // store enable \
.AMPREF``addr        ( AMPREF``addr       ),  // address \
.AMPREF``wdata       ( AMPREF``wdata      ),  // write data \
.AMPREF``wstrb       ( AMPREF``wstrb      ),  // write data \
.AMPREF``rdata       ( AMPREF``rdata      )   // read data \

//
// NPU AM memory wire declaration
//
`define AMWIRES(AMLANES,AMPREF) \
logic         [AMLANES-1:0] AMPREF``mem_en;  // load enable \
logic         [AMLANES-1:0] AMPREF``ls;      // light sleep \
logic         [AMLANES-1:0] AMPREF``ds;      // deep sleep \
logic         [AMLANES-1:0] AMPREF``ldst_en; // store enable \
am_addr_t     [AMLANES-1:0] AMPREF``addr;    // address \
vyixacc_t     [AMLANES-1:0] AMPREF``wdata;   // write data \
vyixacc_t     [AMLANES-1:0] AMPREF``rdata    // read data \

`define AMWIRES_MSK(AMLANES,AMPREF) \
logic         [AMLANES-1:0] AMPREF``mem_en;  // load enable \
logic         [AMLANES-1:0] AMPREF``ls;      // light sleep \
logic         [AMLANES-1:0] AMPREF``ds;      // deep sleep \
logic         [AMLANES-1:0] AMPREF``ldst_en; // store enable \
am_addr_t     [AMLANES-1:0] AMPREF``addr;    // address \
vyixacc_t     [AMLANES-1:0] AMPREF``wdata;   // write data \
ixambit_t     [AMLANES-1:0] AMPREF``wstrb;   // write data \
vyixacc_t     [AMLANES-1:0] AMPREF``rdata    // read data \

`endif
