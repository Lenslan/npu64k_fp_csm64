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
// File defining macros for a parameterizable VM interface
// Parameters to control the instantiation
// - VMPREF:   prefix of the VM interface
// - VMWPREF:  prefix of the wires connected to an VM interface instance (VMINST)
// - VMLANES:  number parallel lanes to VM
//
// Here is an example of how to use these macros:
//import npu_types::*;
//
//`include "npu_vm_macros.svh"
//
//// create a module with an VM master and slave interface
//module t(
//         `VMRMST(2, vmm_),        // two VM master lanes read-only
//         `VMWSLV(3, vms_),        // three VM slave lanes write-only
//         input logic clk
//         );
//endmodule : t
//
//// create a module instantiating two VM interfaces and connecting to a submodule
//module top();
//    logic clk;
//    `VMRWIRES(2,vmi_);
//    `VMWWIRES(3,vsi_);
//
//    t inst(
//           `VMRINST(2,vmm_,vmi_),
//           `VMWINST(3,vms_,vsi_),
//           .clk(clk)
//           );
//endmodule : top

`ifndef NPU_VM_MACROS_INCLUDED
`define NPU_VM_MACROS_INCLUDED


//
// NPU VM read-only wire declaration
//
`define VMRWIRES(VMLANES,VMPREF) \
// command channel \
logic          [VMLANES-1:0] VMPREF``cmd_valid;  // read command valid \
logic          [VMLANES-1:0] VMPREF``cmd_accept; // read command accept \
vm_addr_t      [VMLANES-1:0] VMPREF``cmd_addr;   // read command address \
// read data channel \
logic          [VMLANES-1:0] VMPREF``rvalid;     // read data valid \
ixpix_t        [VMLANES-1:0] VMPREF``rdata       // read data \


//
// NPU VM read-only instance port list
//
// Batch connection
`define VMRINST_B(VMPREF,VMWPREF) \
// read command channel \
.VMPREF``cmd_valid  ( VMWPREF``cmd_valid  ),  // read command valid \
.VMPREF``cmd_accept ( VMWPREF``cmd_accept ),  // read command accept \
.VMPREF``cmd_addr   ( VMWPREF``cmd_addr   ),  // read command address \
// read data channel \
.VMPREF``rvalid     ( VMWPREF``rvalid     ),  // read data valid \
.VMPREF``rdata      ( VMWPREF``rdata      )   // read data \

// Ports connection
`define VMRINST_S(VMLANES,VMPREF,VMWPREF,IDX) \
// read command channel \
.VMPREF``cmd_valid  ( VMWPREF``cmd_valid[IDX+:VMLANES] ),  // read command valid \
.VMPREF``cmd_accept ( VMWPREF``cmd_accept[IDX+:VMLANES]),  // read command accept \
.VMPREF``cmd_addr   ( VMWPREF``cmd_addr[IDX+:VMLANES]  ),  // read command address \
// read data channel \
.VMPREF``rvalid     ( VMWPREF``rvalid[IDX+:VMLANES]    ),  // read data valid \
.VMPREF``rdata      ( VMWPREF``rdata[IDX+:VMLANES]     )   // read data \


//
// NPU VM read-only module master port list
//
`define VMRMST(VMLANES,VMPREF) \
// command channel \
output logic          [VMLANES-1:0] VMPREF``cmd_valid,  // read command valid \
input  logic          [VMLANES-1:0] VMPREF``cmd_accept, // read command accept \
output vm_addr_t      [VMLANES-1:0] VMPREF``cmd_addr,   // read command address \
// read data channel \
input  logic          [VMLANES-1:0] VMPREF``rvalid,     // read data valid \
input  ixpix_t        [VMLANES-1:0] VMPREF``rdata       // read data \


//
// NPU VM read-only module slave port list
//
`define VMRSLV(VMLANES,VMPREF) \
// command channel \
input  logic          [VMLANES-1:0] VMPREF``cmd_valid,  // read command valid \
output logic          [VMLANES-1:0] VMPREF``cmd_accept, // read command accept \
input  vm_addr_t      [VMLANES-1:0] VMPREF``cmd_addr,   // read command address \
// read data channel \
output logic          [VMLANES-1:0] VMPREF``rvalid,     // read data valid \
output ixpix_t        [VMLANES-1:0] VMPREF``rdata       // read data \


//
// NPU VM write-only wire declaration
//
`define VMWWIRES(VMLANES,VMPREF) \
// command channel \
logic          [VMLANES-1:0] VMPREF``cmd_valid;  // write command valid \
logic          [VMLANES-1:0] VMPREF``cmd_accept; // write command accept \
vm_addr_t      [VMLANES-1:0] VMPREF``cmd_addr;   // write command address \
// write data channel \
ixpix_t        [VMLANES-1:0] VMPREF``wdata;      // write data \
ixbit_t        [VMLANES-1:0] VMPREF``wstrb       // write strobe per pixel \


//
// NPU VM write-only instance port list
//
// Batch connection
`define VMWINST_B(VMPREF,VMWPREF) \
// write command channel \
.VMPREF``cmd_valid  ( VMWPREF``cmd_valid  ),  // write command valid \
.VMPREF``cmd_accept ( VMWPREF``cmd_accept ),  // write command accept \
.VMPREF``cmd_addr   ( VMWPREF``cmd_addr   ),  // write command address \
// write data channel \
.VMPREF``wdata      ( VMWPREF``wdata      ),  // write data \
.VMPREF``wstrb      ( VMWPREF``wstrb      )   // write strobe per pixel \

// Ports connection
`define VMWINST_S(VMLANES,VMPREF,VMWPREF,IDX) \
// write command channel \
.VMPREF``cmd_valid  ( VMWPREF``cmd_valid[IDX+:VMLANES]  ),  // write command valid \
.VMPREF``cmd_accept ( VMWPREF``cmd_accept[IDX+:VMLANES] ),  // write command accept \
.VMPREF``cmd_addr   ( VMWPREF``cmd_addr[IDX+:VMLANES]   ),  // write command address \
// write data channel \
.VMPREF``wdata      ( VMWPREF``wdata[IDX+:VMLANES]      ),  // write data \
.VMPREF``wstrb      ( VMWPREF``wstrb[IDX+:VMLANES]      )   // write strobe per pixel \


//
// NPU VM write-only module master port list
//
`define VMWMST(VMLANES,VMPREF) \
// command channel \
output logic          [VMLANES-1:0] VMPREF``cmd_valid,  // write command valid \
input  logic          [VMLANES-1:0] VMPREF``cmd_accept, // write command accept \
output vm_addr_t      [VMLANES-1:0] VMPREF``cmd_addr,   // write command address \
// write data channel \
output ixpix_t        [VMLANES-1:0] VMPREF``wdata,      // write data \
output ixbit_t        [VMLANES-1:0] VMPREF``wstrb       // write strobe per pixel \


//
// NPU VM write-only module slave port list
//
`define VMWSLV(VMLANES,VMPREF) \
// command channel \
input  logic          [VMLANES-1:0] VMPREF``cmd_valid,  // write command valid \
output logic          [VMLANES-1:0] VMPREF``cmd_accept, // write command accept \
input  vm_addr_t      [VMLANES-1:0] VMPREF``cmd_addr,   // write command address \
// write data channel \
input ixpix_t         [VMLANES-1:0] VMPREF``wdata,      // write data \
input ixbit_t         [VMLANES-1:0] VMPREF``wstrb       // write strobe per pixel \

//
// NPU vm memory module master port list
//
`define VMMST(VMLANES,VMPREF) \
output logic          [VMLANES-1:0] VMPREF``mem_en,  // load enable \
output logic          [VMLANES-1:0] VMPREF``ls,      // light sleep enable\
output logic          [VMLANES-1:0] VMPREF``ds,      // deep sleep enable\
output logic          [VMLANES-1:0] VMPREF``ldst_en, // store enable\
output vm_addr_t      [VMLANES-1:0] VMPREF``addr,    // command address \
output ixpix_t        [VMLANES-1:0] VMPREF``wdata,   // write data \
output ixbit_t        [VMLANES-1:0] VMPREF``wstrb,   // write strobe per pixel \
input  ixpix_t        [VMLANES-1:0] VMPREF``rdata    // read data \

//
// NPU vm memory module master port list
//
`define VMSLV(VMLANES,VMPREF) \
input  logic          [VMLANES-1:0] VMPREF``mem_en,  // load enable\
input  logic          [VMLANES-1:0] VMPREF``ls,      // light sleep enable\
input  logic          [VMLANES-1:0] VMPREF``ds,      // deep sleep enable\
input  logic          [VMLANES-1:0] VMPREF``ldst_en, // store enable\
input  vm_addr_t      [VMLANES-1:0] VMPREF``addr,    // command address \
input  ixpix_t        [VMLANES-1:0] VMPREF``wdata,   // write data \
input  ixbit_t        [VMLANES-1:0] VMPREF``wstrb,   // write strobe per pixel \
output ixpix_t        [VMLANES-1:0] VMPREF``rdata    // read data \

//
// NPU VM memory instance port list
//
`define VMINST(VMLANES,VMPREF) \
.VMPREF``mem_en     ( VMPREF``mem_en     ),  // load enable \
.VMPREF``ls         ( VMPREF``ls         ),  // light sleep enable \
.VMPREF``ds         ( VMPREF``ds         ),  // deep sleep enable \
.VMPREF``ldst_en    ( VMPREF``ldst_en    ),  // store enable \
.VMPREF``addr       ( VMPREF``addr       ),  // address \
.VMPREF``wdata      ( VMPREF``wdata      ),  // write data \
.VMPREF``wstrb      ( VMPREF``wstrb      ),  // write strobe per pixel \
.VMPREF``rdata      ( VMPREF``rdata      )   // read data \

//
// NPU VM memory wire declaration
//
`define VMWIRES(VMLANES,VMPREF) \
logic         [VMLANES-1:0] VMPREF``mem_en;  // load enable \
logic         [VMLANES-1:0] VMPREF``ls;      // light sleep \
logic         [VMLANES-1:0] VMPREF``ds;      // deep sleep \
logic         [VMLANES-1:0] VMPREF``ldst_en; // store enable \
vm_addr_t     [VMLANES-1:0] VMPREF``addr;    // address \
ixpix_t       [VMLANES-1:0] VMPREF``wdata;   // write data \
ixbit_t       [VMLANES-1:0] VMPREF``wstrb;   // write strobe per pixel \
ixpix_t       [VMLANES-1:0] VMPREF``rdata    // read data \

//
// NPU VM2AXI wire declaration
//
`define VMAXIWIRES(VMPREFA,VMPREFB) \
logic          VMPREFA``2``VMPREFB``_rvalid;  // \
logic          VMPREFA``2``VMPREFB``_wvalid;  // \
logic          VMPREFB``2``VMPREFA``_rvalid;  // \
logic          VMPREFB``2``VMPREFA``_wvalid;  // \
vm_addr_t      VMPREFB``2``VMPREFA``_addr;   // \
ixpix_t        VMPREFB``2``VMPREFA``_wdata;  // \
ixbit_t        VMPREFB``2``VMPREFA``_wstrb;  //  \
logic    [4:0] VMPREFB``2``VMPREFA``_bank;   // \
ixpix_t        VMPREFA``2``VMPREFB``_rdata   // \

`define VMAXI(VMPREFA,VMPREFB) \
output logic          VMPREFA``2``VMPREFB``_rvalid,  // \
output logic          VMPREFA``2``VMPREFB``_wvalid,  // \
input  logic          VMPREFB``2``VMPREFA``_rvalid,  // \
input  logic          VMPREFB``2``VMPREFA``_wvalid,  // \
input  vm_addr_t      VMPREFB``2``VMPREFA``_addr,   // \
input  ixpix_t        VMPREFB``2``VMPREFA``_wdata,  // \
input  ixbit_t        VMPREFB``2``VMPREFA``_wstrb,  //  \
input  logic    [4:0] VMPREFB``2``VMPREFA``_bank,   // \
output ixpix_t        VMPREFA``2``VMPREFB``_rdata   // \

`define AXIVM(VMPREFA,VMPREFB) \
input  logic          VMPREFA``2``VMPREFB``_rvalid,  // \
input  logic          VMPREFA``2``VMPREFB``_wvalid,  // \
output logic          VMPREFB``2``VMPREFA``_rvalid,  // \
output logic          VMPREFB``2``VMPREFA``_wvalid,  // \
output vm_addr_t      VMPREFB``2``VMPREFA``_addr,   // \
output ixpix_t        VMPREFB``2``VMPREFA``_wdata,  // \
output ixbit_t        VMPREFB``2``VMPREFA``_wstrb,  //  \
output logic    [4:0] VMPREFB``2``VMPREFA``_bank,   // \
input  ixpix_t        VMPREFA``2``VMPREFB``_rdata   // \

`define VMAXIINST(VMPREFA,VMPREFB) \
.VMPREFA``2``VMPREFB``_rvalid  (VMPREFA``2``VMPREFB``_rvalid), // \
.VMPREFA``2``VMPREFB``_wvalid  (VMPREFA``2``VMPREFB``_wvalid), // \
.VMPREFB``2``VMPREFA``_rvalid  (VMPREFB``2``VMPREFA``_rvalid), // \
.VMPREFB``2``VMPREFA``_wvalid  (VMPREFB``2``VMPREFA``_wvalid), // \
.VMPREFB``2``VMPREFA``_addr    (VMPREFB``2``VMPREFA``_addr  ), // \
.VMPREFB``2``VMPREFA``_wdata   (VMPREFB``2``VMPREFA``_wdata ), // \
.VMPREFB``2``VMPREFA``_wstrb   (VMPREFB``2``VMPREFA``_wstrb ), // \
.VMPREFB``2``VMPREFA``_bank    (VMPREFB``2``VMPREFA``_bank  ), // \
.VMPREFA``2``VMPREFB``_rdata   (VMPREFA``2``VMPREFB``_rdata )  // \

`endif
