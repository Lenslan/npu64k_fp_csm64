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
//`include "npu_vm_ecc_macros.sv"
//
//// create a module with an VM master and slave interface
//module t(
//         `VMRMST_ECC(2, vmm_),        // two VM master lanes read-only
//         `VMWSLV_ECC(3, vms_),        // three VM slave lanes write-only
//         input logic clk
//         );
//endmodule : t
//
//// create a module instantiating two VM interfaces and connecting to a submodule
//module top();
//    logic clk;
//    `VMRWIRES_ECC(2,vmi_);
//    `VMWWIRES_ECC(3,vsi_);
//
//    t inst(
//           `VMRINST_ECC(2,vmm_,vmi_),
//           `VMWINST_ECC(3,vms_,vsi_),
//           .clk(clk)
//           );
//endmodule : top

`ifndef NPU_VM_ECC_MACROS_INCLUDED
`define NPU_VM_ECC_MACROS_INCLUDED

//
// NPU VM read-only wire declaration
//
`define VMRWIRES_ECC(VMLANES,VMPREF) \
vm_ecc_c_t  [VMLANES-1:0]                  VMPREF``ecc             // vm ecc check bit \
//// err report \
//logic       [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``sb_err;         // vm ecc single bit error signal \
//logic       [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``db_err;         // vm ecc double bit error signal \
//vm_ecc_s_t  [VMLANES-1:0]                  VMPREF``syndrome        // vm ecc syndrome \    

`define VMRWIRES_ECC_ONLY(VMLANES,VMPREF) \
vm_ecc_c_t  [VMLANES-1:0]                  VMPREF``ecc   // vm ecc check bit \

`define VMRWIRES_ECC_RPT(VMLANES,VMPREF) \
// err report \
logic       [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``sb_err;      // vm ecc single bit error signal \
logic       [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``db_err;      // vm ecc double bit error signal \
vm_ecc_s_t  [VMLANES-1:0]                  VMPREF``syndrome     // vm ecc syndrome \


//
// NPU VM read-only instance port list
//
// Batch connection
`define VMRINST_ECC_B(VMPREF,VMWPREF) \
.VMPREF``ecc            ( VMWPREF``ecc            )  // vm ecc check bit \
//// err report \
//.VMPREF``sb_err         ( VMWPREF``sb_err         ), // vm ecc single bit error signal \
//.VMPREF``db_err         ( VMWPREF``db_err         ), // vm ecc double bit error signal \
//.VMPREF``syndrome       ( VMWPREF``syndrome       )  // vm ecc syndrome \

`define VMRINST_ECC_ONLY_B(VMPREF,VMWPREF) \
.VMPREF``ecc            ( VMWPREF``ecc            )  // vm ecc check bit \

`define VMRINST_ECC_RPT_B(VMPREF,VMWPREF) \
.VMPREF``sb_err       ( VMWPREF``sb_err      ), // vm ecc single bit error signal \
.VMPREF``db_err       ( VMWPREF``db_err      ), // vm ecc double bit error signal \
.VMPREF``syndrome     ( VMWPREF``syndrome    )  // vm ecc syndrome \


// Ports connection
`define VMRINST_ECC_S(VMLANES,VMPREF,VMWPREF,IDX) \
.VMPREF``ecc            ( VMWPREF``ecc[IDX+:VMLANES]            )  // vm ecc check bit \
//// error report \
//.VMPREF``sb_err         ( VMWPREF``sb_err[IDX+:VMLANES]         ), // vm ecc single bit error signal \
//.VMPREF``db_err         ( VMWPREF``db_err[IDX+:VMLANES]         ), // vm ecc double bit error signal \
//.VMPREF``syndrome       ( VMWPREF``syndrome[IDX+:VMLANES]       )  // vm ecc syndrome \

`define VMRINST_ECC_ONLY_S(VMLANES,VMPREF,VMWPREF,IDX) \
.VMPREF``ecc            ( VMWPREF``ecc[IDX+:VMLANES]            )  // vm ecc check bit \

`define VMRINST_ECC_RPT_S(VMLANES,VMPREF,VMWPREF,IDX) \
.VMPREF``sb_err       ( VMWPREF``sb_err[IDX+:VMLANES]      ), // vm ecc single bit error signal \
.VMPREF``db_err       ( VMWPREF``db_err[IDX+:VMLANES]      ), // vm ecc double bit error signal \
.VMPREF``syndrome     ( VMWPREF``syndrome[IDX+:VMLANES]    )  // vm ecc syndrome \


//
// NPU VM read-only module slave ecc port list
//
`define VMRSLV_ECC(VMLANES,VMPREF) \
input  vm_ecc_c_t [VMLANES-1:0]                  VMPREF``ecc       // vm ecc check bit \
//// error report \
//output logic      [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``sb_err,   // vm ecc single bit error signal \
//output logic      [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``db_err,   // vm ecc double bit error signal \
//output vm_ecc_s_t [VMLANES-1:0]                  VMPREF``syndrome  // vm ecc syndrome \

`define VMRSLV_ECC_ONLY(VMLANES,VMPREF) \
input  vm_ecc_c_t [VMLANES-1:0]                  VMPREF``ecc       // vm ecc check bit \

`define VMRSLV_ECC_RPT(VMLANES,VMPREF) \
output logic      [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``sb_err,   // vm ecc single bit error signal \
output logic      [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``db_err,   // vm ecc double bit error signal \
output vm_ecc_s_t [VMLANES-1:0]                  VMPREF``syndrome  // vm ecc syndrome \


//
// NPU VM read-only module master port list
//
`define VMRMST_ECC(VMLANES,VMPREF) \
output vm_ecc_c_t [VMLANES-1:0] VMPREF``ecc             // vm ecc check bit \


//
// NPU VM write-only wire declaration
//
`define VMWWIRES_ECC(VMLANES,VMPREF) \
vm_ecc_c_t        [VMLANES-1:0] VMPREF``ecc             // write ecc bits \


//
// NPU VM write-only instance port list
//
// Batch connection
`define VMWINST_ECC_B(VMPREF,VMWPREF) \
.VMPREF``ecc            ( VMWPREF``ecc            )  // write ecc bits \


// Ports connection
`define VMWINST_ECC_S(VMLANES,VMPREF,VMWPREF,IDX) \
.VMPREF``ecc            ( VMWPREF``ecc[IDX+:VMLANES]            )  // write ecc bits \


//
// NPU VM write-only module master port list
//
`define VMWMST_ECC(VMLANES,VMPREF) \
output vm_ecc_c_t [VMLANES-1:0] VMPREF``ecc  // write ecc bits \


//
// NPU VM write-only module slave port list
//
`define VMWSLV_ECC(VMLANES,VMPREF) \
input  vm_ecc_c_t     [VMLANES-1:0] VMPREF``ecc             // write ecc bits \ 


//
// NPU vm memory module master port list
//
`define VMMST_ECC(VMLANES,VMPREF) \
output vm_ecc_c_t [VMLANES-1:0] VMPREF``wecc,  // write ecc \
output            [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``ecc_wstrb, \
input  vm_ecc_c_t [VMLANES-1:0] VMPREF``recc   // read ecc \

//
// NPU vm memory module master port list
//
`define VMSLV_ECC(VMLANES,VMPREF) \
input  vm_ecc_c_t [VMLANES-1:0] VMPREF``wecc,  // write ecc \
input            [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``ecc_wstrb,  \
output vm_ecc_c_t [VMLANES-1:0] VMPREF``recc   // read ecc \

//
// NPU VM memory instance port list
//
`define VMINST_ECC(VMLANES,VMPREF) \
.VMPREF``wecc      ( VMPREF``wecc ),  // write ecc \
.VMPREF``ecc_wstrb ( VMPREF``ecc_wstrb ),  \
.VMPREF``recc      ( VMPREF``recc )   // read ecc \

//
// NPU VM memory wire declaration
//
`define VMWIRES_ECC(VMLANES,VMPREF) \
vm_ecc_c_t       [VMLANES-1:0] VMPREF``wecc;  // write ecc \
logic            [VMLANES-1:0] [VM_NUM_ECC-1:0] VMPREF``ecc_wstrb;  \
vm_ecc_c_t       [VMLANES-1:0] VMPREF``recc   // read ecc \

`endif


// NPU VM memory read ports ecc decoder port list
`define VM_ECC_DEC(ECC_NUM) \
input clk, \
input rst_a, \
input [1:0] vm_prot_en, \
input error_mask, \
input ql, \
input [VM_ECC_UNIT_DW*ECC_NUM-1:0] data_in, \
input vm_addr_t address,  \
input vm_ecc_unit_c_t [ECC_NUM-1:0] ecc_in,  \
output fatal_err \
`endif

