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
// - AMLANES:  number parallel lanes to AM
//
// Here is an example of how to use these macros:
//
//import npu_types::*;
//
//`include "npu_am_ecc_macros.sv"
//
//// create a module with an AM master and slave interface
//module t(
//         `AMRMST_ECC(amm_),        // two AM master lanes read-only
//         `AMWSLV_ECC(ams_),        // three AM slave lanes write-only
//         input logic clk
//         );
//endmodule : t
//
//// create a module instantiating two AM interfaces and connecting to a submodule
//module top();
//    logic clk;
//    `AMRWIRES_ECC(ami_);
//    `AMWWIRES_ECC(vsi_);
//
//    t inst(
//           `AMRINST_ECC(amm_,ami_),
//           `AMWINST_ECC(ams_,vsi_),
//           .clk(clk)
//           );
//endmodule : top

`ifndef NPU_AM_ECC_MACROS_INCLUDED
`define NPU_AM_ECC_MACROS_INCLUDED

//
// NPU AM read-only wire declaration
//
`define AMRWIRES_ECC(AMPREF,N) \
am_ecc_c_t [N-1:0]                  AMPREF``ecc             // am ecc check bit \
//// err report \
//logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``sb_err;         // am ecc single bit error signal \
//logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``db_err;         // am ecc double bit error signal \
//am_ecc_s_t [N-1:0]                  AMPREF``syndrome        // am ecc syndrome \

`define AMRWIRES_ECC_ONLY(AMPREF,N) \
am_ecc_c_t [N-1:0]                  AMPREF``ecc             // am ecc check bit \

`define AMRWIRES_ECC_RPT(AMPREF,N) \
logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``sb_err;         // am ecc single bit error signal \
logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``db_err;         // am ecc double bit error signal \
am_ecc_s_t [N-1:0]                  AMPREF``syndrome        // am ecc syndrome \

`define AMRWIRES_E2E(AMPREF,N) \

//
// NPU AM read-only instance port list
//
// Batch connection
`define AMRINST_ECC_B(AMPREF,AMWPREF) \
.AMPREF``ecc            ( AMWPREF``ecc            )  // am ecc check bit \
//// err report \
//.AMPREF``sb_err         ( AMWPREF``sb_err         ), // am ecc single bit error signal \
//.AMPREF``db_err         ( AMWPREF``db_err         ), // am ecc double bit error signal \
//.AMPREF``syndrome       ( AMWPREF``syndrome       )  // am ecc syndrome \

`define AMRINST_ECC_ONLY_B(AMPREF,AMWPREF) \
.AMPREF``ecc            ( AMWPREF``ecc            )  // am ecc check bit \

`define AMRINST_ECC_RPT_B(AMPREF,AMWPREF) \
.AMPREF``sb_err         ( AMWPREF``sb_err         ), // am ecc single bit error signal \
.AMPREF``db_err         ( AMWPREF``db_err         ), // am ecc double bit error signal \
.AMPREF``syndrome       ( AMWPREF``syndrome       )  // am ecc syndrome \


// Ports connection
`define AMRINST_ECC_S(AMPREF,AMWPREF,N) \
.AMPREF``ecc            ( AMWPREF``ecc[N]            )  // am ecc check bit \
//// err report \
//.AMPREF``sb_err         ( AMWPREF``sb_err[N]         ), // am ecc single bit error signal \
//.AMPREF``db_err         ( AMWPREF``db_err[N]         ), // am ecc double bit error signal \
//.AMPREF``syndrome       ( AMWPREF``syndrome[N]       )  // am ecc syndrome \

`define AMRINST_ECC_ONLY_S(AMPREF,AMWPREF,N) \
.AMPREF``ecc            ( AMWPREF``ecc[N]            )  // am ecc check bit \
 
`define AMRINST_ECC_RPT_S(AMPREF,AMWPREF,LANES,IDX) \
.AMPREF``sb_err       ( AMWPREF``sb_err[IDX+:LANES]      ), // am ecc single bit error signal \
.AMPREF``db_err       ( AMWPREF``db_err[IDX+:LANES]      ), // am ecc double bit error signal \
.AMPREF``syndrome     ( AMWPREF``syndrome[IDX+:LANES]    )  // am ecc syndrome \

`define AMRINST_ECC_RPT_N(AMPREF,AMWPREF,N) \
.AMPREF``sb_err       ( AMWPREF``sb_err[N]      ), // am ecc single bit error signal \
.AMPREF``db_err       ( AMWPREF``db_err[N]      ), // am ecc double bit error signal \
.AMPREF``syndrome     ( AMWPREF``syndrome[N]    )  // am ecc syndrome \


//
// NPU AM read-only module slave ecc port list
//
`define AMRSLV_ECC(AMPREF,N) \
input  am_ecc_c_t [N-1:0]                  AMPREF``ecc             // am ecc check bit \
//// error report \
//output logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``sb_err,         // am ecc single bit error signal \
//output logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``db_err,         // am ecc double bit error signal \
//output am_ecc_s_t [N-1:0]                  AMPREF``syndrome        // am ecc syndrome \

`define AMRSLV_ECC_ONLY(AMPREF,N) \
input  am_ecc_c_t [N-1:0]                  AMPREF``ecc             // am ecc check bit \

`define AMRSLV_ECC_RPT(AMPREF,N) \
output logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``sb_err,         // am ecc single bit error signal \
output logic      [N-1:0] [AM_NUM_ECC-1:0] AMPREF``db_err,         // am ecc double bit error signal \
output am_ecc_s_t [N-1:0]                  AMPREF``syndrome        // am ecc syndrome \

 
//
// NPU AM read-only module master port list
//
`define AMRMST_ECC(AMPREF, N) \
output am_ecc_c_t [N-1:0] AMPREF``ecc             // am ecc check bit \

 
//
// NPU AM write-only wire declaration
//
`define AMWWIRES_ECC(AMPREF, N) \
am_ecc_c_t        [N-1:0] AMPREF``ecc             // write ecc bits \

`define AMWWIRES_MSK_ECC(AMPREF, N) \
am_ecc_c_t        [N-1:0] AMPREF``ecc             // write ecc bits \


//
// NPU AM write-only instance port list
//
// Batch connection
`define AMWINST_ECC_B(AMPREF,AMWPREF) \
.AMPREF``ecc            ( AMWPREF``ecc            )  // write ecc bits \

`define AMWINST_ECC_B_MSK(AMPREF,AMWPREF) \
.AMPREF``ecc            ( AMWPREF``ecc            )  // write ecc bits \


// Ports connection
`define AMWINST_ECC_S(AMPREF,AMWPREF,N) \
.AMPREF``ecc            ( AMWPREF``ecc[N]            )  // write ecc bits \


//
// NPU AM write-only module master port list
//
`define AMWMST_ECC(AMPREF, N) \
output am_ecc_c_t     [N-1:0] AMPREF``ecc  // write ecc bits \

`define AMWMST_MSK_ECC(AMPREF, N) \
output am_ecc_c_t     [N-1:0] AMPREF``ecc  // write ecc bits \


//
// NPU AM write-only module slave port list
//
`define AMWSLV_ECC(AMPREF, N) \
input  am_ecc_c_t     [N-1:0] AMPREF``ecc  // write ecc bits \ 

`define AMWSLV_MSK_ECC(AMPREF, N) \
input  am_ecc_c_t     [N-1:0] AMPREF``ecc  // write ecc bits \

//
// NPU am memory module master port list
//
`define AMMST_ECC(AMLANES,AMPREF) \
output am_ecc_c_t [AMLANES-1:0] AMPREF``wecc,  // write ecc \
output            [AMLANES-1:0] [AM_NUM_ECC-1:0] AMPREF``ecc_wstrb, \
input  am_ecc_c_t [AMLANES-1:0] AMPREF``recc   // read ecc \

//
// NPU am memory module master port list
//
`define AMSLV_ECC(AMLANES,AMPREF) \
input  am_ecc_c_t [AMLANES-1:0] AMPREF``wecc,  // write ecc \
input             [AMLANES-1:0] [AM_NUM_ECC-1:0] AMPREF``ecc_wstrb,  \
output am_ecc_c_t [AMLANES-1:0] AMPREF``recc   // read ecc \

//
// NPU AM memory instance port list
//
`define AMINST_ECC(AMLANES,AMPREF) \
.AMPREF``wecc      ( AMPREF``wecc ),  // write ecc \
.AMPREF``ecc_wstrb ( AMPREF``ecc_wstrb ),  \
.AMPREF``recc      ( AMPREF``recc )   // read ecc \

//
// NPU AM memory wire declaration
//
`define AMWIRES_ECC(AMLANES,AMPREF) \
am_ecc_c_t       [AMLANES-1:0] AMPREF``wecc;  // write ecc \
logic            [AMLANES-1:0] [AM_NUM_ECC-1:0] AMPREF``ecc_wstrb;  \
am_ecc_c_t       [AMLANES-1:0] AMPREF``recc   // read ecc \

`endif



// NPU AM memory read ports ecc decoder port list
`define AM_ECC_DEC(ECC_NUM) \
input clk, \
input rst_a, \
input [1:0] am_prot_en, \
input error_mask, \
input ql, \
input [AM_ECC_UNIT_DW*ECC_NUM-1:0] data_in, \
input am_addr_t address,  \
input am_ecc_unit_c_t [ECC_NUM-1:0] ecc_in,  \
output fatal_err \
`endif

