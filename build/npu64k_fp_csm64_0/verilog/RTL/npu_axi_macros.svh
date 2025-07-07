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
// File defining macros for an AXI4 interface
// Parameters to control the instantiation
// - AXIPREF:   prefix of the AXI interface
// - AXIWPREF:  prefix of the wires connected to an AXI instance (AXIINST)
// - AXIIDW:    number of bits in the ID vector (>0)
// - AXIDW:     number of bits in the data vector (>=8, power of 2)
// - AXIAWUW:   number of bits in the write command user field (>0)
// - AXIWUW:    number of bits in the write data user field (>0)
// - AXIBUW:    number of bits in the write response user field (>0)
// - AXIARUW:   number of bits in the read command user field (>0)
// - AXIRUW:    number of bits in the read data user field (>0)
//
// Here is an example of how to use these macros:
//import npu_types::*;
//
//`include "npu_axi_macros.svh"
//
//// create a module with an AXI master and slave interface
//module t(
//         `AXIMST(2,1,3,2,1,2,1,axim_),
//         `AXISLV(2,1,5,2,1,2,1,axis_),
//         input logic clk
//         );
//endmodule : t
//
//// create a module instantiating two AXI interfaces and connecting to a submodule
//module top();
//    logic clk;
//    `AXIWIRES(2,1,3,2,1,2,1,aximi_);
//    `AXIWIRES(2,1,5,2,1,2,1,axisi_);
//
//    t inst(
//           `AXIINST(2,1,3,2,1,2,1,axim_,aximi_),
//           `AXIINST(2,1,5,2,1,2,1,axis_,axisi_),
//           .clk(clk)
//           );
//endmodule : top

`ifndef NPU_AXI_MACROS_INCLUDED
`define NPU_AXI_MACROS_INCLUDED

// ----------------------------------------------------------------------------
// Wire declaration
// ----------------------------------------------------------------------------

//
// NPU AXI wire declaration
//  Using packed structures types (npu_axi_cmd_t / npu_axi_resp_t)
//
`define AXIWIRES(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic                        AXIPREF``arvalid; // read command valid \
logic                        AXIPREF``arready; // read command accept \
logic          [AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_cmd_t                AXIPREF``ar;      // read command \
// read data channel \
logic                        AXIPREF``rvalid;  // read data valid \
logic                        AXIPREF``rready;  // read data accept \
logic          [AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [AXIDW-1:0]   AXIPREF``rdata;   // read data \
npu_axi_resp_t               AXIPREF``rresp;   // read response \
logic          [AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic                        AXIPREF``rlast;   // read last \
// write command channel \
logic                        AXIPREF``awvalid; // write command valid \
logic                        AXIPREF``awready; // write command accept \
logic          [AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_cmd_t                AXIPREF``aw;      // write command \
// write data channel \
logic                        AXIPREF``wvalid;  // write data valid \
logic                        AXIPREF``wready;  // write data accept \
logic          [AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic                        AXIPREF``wlast;   // write data last \
// write response channel \
logic                        AXIPREF``bvalid;  // write response valid \
logic                        AXIPREF``bready;  // write response accept \
logic          [AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t               AXIPREF``bresp    // write response \

//
// NPU AXI wire declaration
//  Array of N interfaces, using packed structure types
//
`define AXIWIRESN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic          [N-1:0]              AXIPREF``arvalid; // read command valid \
logic          [N-1:0]              AXIPREF``arready; // read command accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_cmd_t  [N-1:0]              AXIPREF``ar;      // read command \
// read data channel \
logic          [N-1:0]              AXIPREF``rvalid;  // read data valid \
logic          [N-1:0]              AXIPREF``rready;  // read data accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [N-1:0][AXIDW-1:0]   AXIPREF``rdata;   // read data \
npu_axi_resp_t [N-1:0]              AXIPREF``rresp;   // read response \
logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic          [N-1:0]              AXIPREF``rlast;   // read last \
// write command channel \
logic          [N-1:0]              AXIPREF``awvalid; // write command valid \
logic          [N-1:0]              AXIPREF``awready; // write command accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_cmd_t  [N-1:0]              AXIPREF``aw;      // write command \
// write data channel \
logic          [N-1:0]              AXIPREF``wvalid;  // write data valid \
logic          [N-1:0]              AXIPREF``wready;  // write data accept \
logic          [N-1:0][AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [N-1:0][AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic          [N-1:0]              AXIPREF``wlast;   // write data last \
// write response channel \
logic          [N-1:0]              AXIPREF``bvalid;  // write response valid \
logic          [N-1:0]              AXIPREF``bready;  // write response accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \

//
// NPU AXI wire declaration
//  Array of N interfaces, using packed structure types
//
`define AXINODATAWIRESN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic          [N-1:0]              AXIPREF``arvalid; // read command valid \
logic          [N-1:0]              AXIPREF``arready; // read command accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_cmd_t  [N-1:0]              AXIPREF``ar;      // read command \
// read data channel \
logic          [N-1:0]              AXIPREF``rvalid;  // read data valid \
logic          [N-1:0]              AXIPREF``rready;  // read data accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid;     // read data id \
npu_axi_resp_t [N-1:0]              AXIPREF``rresp;   // read response \
logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic          [N-1:0]              AXIPREF``rlast;   // read last \
// write command channel \
logic          [N-1:0]              AXIPREF``awvalid; // write command valid \
logic          [N-1:0]              AXIPREF``awready; // write command accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_cmd_t  [N-1:0]              AXIPREF``aw;      // write command \
// write data channel \
logic          [N-1:0]              AXIPREF``wvalid;  // write data valid \
logic          [N-1:0]              AXIPREF``wready;  // write data accept \
logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic          [N-1:0]              AXIPREF``wlast;   // write data last \
// write response channel \
logic          [N-1:0]              AXIPREF``bvalid;  // write response valid \
logic          [N-1:0]              AXIPREF``bready;  // write response accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \


//
// AXI wires declaration for external interfaces
//   Packed structures are not used
//   Typedef enum are used
//
`define AXIWIRES_EXT(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic                        AXIPREF``arvalid; // read command valid \
logic                        AXIPREF``arready; // read command accept \
logic          [AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_addr_t               AXIPREF``araddr;  // \
npu_axi_cache_t              AXIPREF``arcache; // \
npu_axi_prot_t               AXIPREF``arprot;  // \
npu_axi_lock_t               AXIPREF``arlock;  // \
npu_axi_burst_t              AXIPREF``arburst; // \
npu_axi_len_t                AXIPREF``arlen;   // \
npu_axi_size_t               AXIPREF``arsize;  // \
npu_axi_region_t             AXIPREF``arregion;// \
// read data channel \
logic                        AXIPREF``rvalid;  // read data valid \
logic                        AXIPREF``rready;  // read data accept \
logic          [AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [AXIDW-1:0]   AXIPREF``rdata;   // read data \
npu_axi_resp_t               AXIPREF``rresp;   // read response \
logic          [AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic                        AXIPREF``rlast;   // read last \
// write command channel \
logic                        AXIPREF``awvalid; // write command valid \
logic                        AXIPREF``awready; // write command accept \
logic          [AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_addr_t               AXIPREF``awaddr;  // \
npu_axi_cache_t              AXIPREF``awcache; // \
npu_axi_prot_t               AXIPREF``awprot;  // \
npu_axi_lock_t               AXIPREF``awlock;  // \
npu_axi_burst_t              AXIPREF``awburst; // \
npu_axi_len_t                AXIPREF``awlen;   // \
npu_axi_size_t               AXIPREF``awsize;  // \
npu_axi_region_t             AXIPREF``awregion;// \
// write data channel \
logic                        AXIPREF``wvalid;  // write data valid \
logic                        AXIPREF``wready;  // write data accept \
logic          [AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic                        AXIPREF``wlast;   // write data last \
// write response channel \
logic                        AXIPREF``bvalid;  // write response valid \
logic                        AXIPREF``bready;  // write response accept \
logic          [AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t               AXIPREF``bresp    // write response \


//
// NPU AXI wire declaration
//   Using only plain logic type for the wires (no packed struct, no typedef)
//
`define AXIWIRES_FLAT(AXIIDW,AXIAW,AXIDW,AXIARGW,AXILEN,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic                        AXIPREF``arvalid; // read command valid \
logic                        AXIPREF``arready; // read command accept \
logic          [AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
logic          [AXIAW-1:0]   AXIPREF``araddr;  // read command address \
logic          [3:0]         AXIPREF``arcache; // \
logic          [2:0]         AXIPREF``arprot;  // \
logic          [0:0]         AXIPREF``arlock;  // \
logic          [1:0]         AXIPREF``arburst; // \
logic          [AXILEN-1:0]  AXIPREF``arlen;   // \
logic          [2:0]         AXIPREF``arsize;  // \
logic          [AXIARGW-1:0] AXIPREF``arregion;// read command region \
// read data channel \
logic                        AXIPREF``rvalid;  // read data valid \
logic                        AXIPREF``rready;  // read data accept \
logic          [AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [AXIDW-1:0]   AXIPREF``rdata;   // read data \
logic          [1:0]         AXIPREF``rresp;   // read response \
logic          [AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic                        AXIPREF``rlast;   // read last \
// write command channel \
logic                        AXIPREF``awvalid; // write command valid \
logic                        AXIPREF``awready; // write command accept \
logic          [AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
logic          [AXIAW-1:0]   AXIPREF``awaddr;  // \
logic          [3:0]         AXIPREF``awcache; // \
logic          [2:0]         AXIPREF``awprot;  // \
logic          [0:0]         AXIPREF``awlock;  // \
logic          [1:0]         AXIPREF``awburst; // \
logic          [AXILEN-1:0]  AXIPREF``awlen;   // \
logic          [2:0]         AXIPREF``awsize;  // \
logic          [AXIARGW-1:0] AXIPREF``awregion;// \
// write data channel \
logic                        AXIPREF``wvalid;  // write data valid \
logic                        AXIPREF``wready;  // write data accept \
logic          [AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic                        AXIPREF``wlast;   // write data last \
// write response channel \
logic                        AXIPREF``bvalid;  // write response valid \
logic                        AXIPREF``bready;  // write response accept \
logic          [AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
logic          [1:0]         AXIPREF``bresp    // write response \

// ----------------------------------------------------------------------------
// Instance port assignment
// ----------------------------------------------------------------------------

//
// NPU AXI instance port assignment
//   Using packed structure types
//
`define AXIINST(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser  ), // read command user field \
.AXIPREF``ar      ( AXIWPREF``ar      ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid     ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata   ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast   ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid    ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser  ), // write command user field \
.AXIPREF``aw      ( AXIWPREF``aw      ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready  ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata   ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb   ), // write data strobe \
.AXIPREF``wuser   ( AXIWPREF``wuser   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid     ), // write response id \
.AXIPREF``buser   ( AXIWPREF``buser   ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp   )  // write response \

//
// NPU AXI instance port assignment
//   Using packed structure types
//
`define AXINODATAINST(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser  ), // read command user field \
.AXIPREF``ar      ( AXIWPREF``ar      ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid     ), // read data id \
.AXIPREF``rresp   ( AXIWPREF``rresp   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast   ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid    ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser  ), // write command user field \
.AXIPREF``aw      ( AXIWPREF``aw      ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready  ), // write data accept \
.AXIPREF``wuser   ( AXIWPREF``wuser   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid     ), // write response id \
.AXIPREF``buser   ( AXIWPREF``buser   ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp   )  // write response \

//
// NPU AXI instance port assignment
//   Module instance has the array interface
//   Connect one of the N interfaces in the array
//   Using packed structure types
//
`define AXIINSTN(N,AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid[N] ( AXIWPREF``arvalid ), // read command valid \
.AXIPREF``arready[N] ( AXIWPREF``arready ), // read command accept \
.AXIPREF``arid[N]    ( AXIWPREF``arid    ), // read command ID \
.AXIPREF``aruser[N]  ( AXIWPREF``aruser  ), // read command user field \
.AXIPREF``ar[N]      ( AXIWPREF``ar      ), // read command \
// read data channel \
.AXIPREF``rvalid[N]  ( AXIWPREF``rvalid  ), // read data valid \
.AXIPREF``rready[N]  ( AXIWPREF``rready  ), // read data accept \
.AXIPREF``rid[N]     ( AXIWPREF``rid     ), // read data id \
.AXIPREF``rdata[N]   ( AXIWPREF``rdata   ), // read data \
.AXIPREF``rresp[N]   ( AXIWPREF``rresp   ), // read response \
.AXIPREF``ruser[N]   ( AXIWPREF``ruser   ), // read data user field \
.AXIPREF``rlast[N]   ( AXIWPREF``rlast   ), // read last \
// write command channel \
.AXIPREF``awvalid[N] ( AXIWPREF``awvalid ), // write command valid \
.AXIPREF``awready[N] ( AXIWPREF``awready ), // write command accept \
.AXIPREF``awid[N]    ( AXIWPREF``awid    ), // write command ID \
.AXIPREF``awuser[N]  ( AXIWPREF``awuser  ), // write command user field \
.AXIPREF``aw[N]      ( AXIWPREF``aw      ), // write command \
// write data channel \
.AXIPREF``wvalid[N]  ( AXIWPREF``wvalid  ), // write data valid \
.AXIPREF``wready[N]  ( AXIWPREF``wready  ), // write data accept \
.AXIPREF``wdata[N]   ( AXIWPREF``wdata   ), // write data \
.AXIPREF``wstrb[N]   ( AXIWPREF``wstrb   ), // write data strobe \
.AXIPREF``wuser[N]   ( AXIWPREF``wuser   ), // write data user field \
.AXIPREF``wlast[N]   ( AXIWPREF``wlast   ), // write data last \
// write response channel \
.AXIPREF``bvalid[N]  ( AXIWPREF``bvalid  ), // write response valid \
.AXIPREF``bready[N]  ( AXIWPREF``bready  ), // write response accept \
.AXIPREF``bid[N]     ( AXIWPREF``bid     ), // write response id \
.AXIPREF``buser[N]   ( AXIWPREF``buser   ), // read data user field \
.AXIPREF``bresp[N]   ( AXIWPREF``bresp   )  // write response \


//
// NPU AXI instance port assignment
//   Module instance has single AXI interface connecting to the array
//   Connect one of the N interfaces in the array
//   Using packed structure types
//
`define AXIINSTM(M,AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid[M] ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready[M] ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid[M]    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser[M]  ), // read command user field \
.AXIPREF``ar      ( AXIWPREF``ar[M]      ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid[M]  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready[M]  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid[M]     ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata[M]   ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp[M]   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser[M]   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast[M]   ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid[M] ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready[M] ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid[M]    ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser[M]  ), // write command user field \
.AXIPREF``aw      ( AXIWPREF``aw[M]      ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid[M]  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready[M]  ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata[M]   ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb[M]   ), // write data strobe \
.AXIPREF``wuser   ( AXIWPREF``wuser[M]   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast[M]   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid[M]  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready[M]  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid[M]     ), // write response id \
.AXIPREF``buser   ( AXIWPREF``buser[M]   ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[M]   )  // write response \

//
// NPU AXI instance port assignment
//   Module instance has single AXI interface connecting to the array
//   Connect one of the N interfaces in the array
//   Using packed structure types
//
`define AXINODATAINSTM(M,AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid[M] ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready[M] ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid[M]    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser[M]  ), // read command user field \
.AXIPREF``ar      ( AXIWPREF``ar[M]      ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid[M]  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready[M]  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid[M]     ), // read data id \
.AXIPREF``rresp   ( AXIWPREF``rresp[M]   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser[M]   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast[M]   ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid[M] ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready[M] ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid[M]    ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser[M]  ), // write command user field \
.AXIPREF``aw      ( AXIWPREF``aw[M]      ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid[M]  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready[M]  ), // write data accept \
.AXIPREF``wuser   ( AXIWPREF``wuser[M]   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast[M]   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid[M]  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready[M]  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid[M]     ), // write response id \
.AXIPREF``buser   ( AXIWPREF``buser[M]   ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[M]   )  // write response \


//
//  NPU AXI instance port assignment
//    For external interfaces that do not use packed struct
//
`define AXIINST_EXT(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser  ), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``araddr  ), // \
.AXIPREF``arcache ( AXIWPREF``arcache ), // \
.AXIPREF``arprot  ( AXIWPREF``arprot  ), // \
.AXIPREF``arlock  ( AXIWPREF``arlock  ), // \
.AXIPREF``arburst ( AXIWPREF``arburst ), // \
.AXIPREF``arlen   ( AXIWPREF``arlen   ), // \
.AXIPREF``arsize  ( AXIWPREF``arsize  ), // \
.AXIPREF``arregion( AXIWPREF``arregion), // \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid     ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata   ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast   ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid    ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser  ), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``awaddr  ), // \
.AXIPREF``awcache ( AXIWPREF``awcache ), // \
.AXIPREF``awprot  ( AXIWPREF``awprot  ), // \
.AXIPREF``awlock  ( AXIWPREF``awlock  ), // \
.AXIPREF``awburst ( AXIWPREF``awburst ), // \
.AXIPREF``awlen   ( AXIWPREF``awlen   ), // \
.AXIPREF``awsize  ( AXIWPREF``awsize  ), // \
.AXIPREF``awregion( AXIWPREF``awregion), // \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready  ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata   ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb   ), // write data strobe \
.AXIPREF``wuser   ( AXIWPREF``wuser   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid     ), // write response id \
.AXIPREF``buser   ( AXIWPREF``buser   ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp   )  // write response \


//
//  NPU AXI instance port assignment (flattening)
//   Using packed structure types wires side, flat on the module interface side
//
`define AXIINST_FLAT(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid  ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready  ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid     ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser   ), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``ar.addr  ), // read command address \
.AXIPREF``arcache ( AXIWPREF``ar.cache ), // \
.AXIPREF``arprot  ( AXIWPREF``ar.prot  ), // \
.AXIPREF``arlock  ( AXIWPREF``ar.lock  ), // \
.AXIPREF``arburst ( AXIWPREF``ar.burst ), // \
.AXIPREF``arlen   ( AXIWPREF``ar.len   ), // \
.AXIPREF``arsize  ( AXIWPREF``ar.size  ), // \
//.AXIPREF``arregion( AXIWPREF``ar.region), // \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid   ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready   ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid      ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata    ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp    ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser    ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast    ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid  ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready  ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid     ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser   ), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``aw.addr  ), // write command address \
.AXIPREF``awcache ( AXIWPREF``aw.cache ), // \
.AXIPREF``awprot  ( AXIWPREF``aw.prot  ), // \
.AXIPREF``awlock  ( AXIWPREF``aw.lock  ), // \
.AXIPREF``awburst ( AXIWPREF``aw.burst ), // \
.AXIPREF``awlen   ( AXIWPREF``aw.len   ), // \
.AXIPREF``awsize  ( AXIWPREF``aw.size  ), // \
//.AXIPREF``awregion( AXIWPREF``aw.region), // \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid   ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready   ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata    ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb    ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser    ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast    ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid   ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready   ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid      ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser    ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp    )  // write response \

`define AXIINST_P2UP(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid  ( AXIWPREF``arvalid  ), // read command valid \
.AXIPREF``arready  ( AXIWPREF``arready  ), // read command accept \
.AXIPREF``arid     ( AXIWPREF``arid     ), // read command ID \
.AXIPREF``aruser   ( AXIWPREF``aruser   ), // read command user field \
.AXIPREF``ar       ( {npu_axi_addr_t'(AXIWPREF``araddr),    \
                      npu_axi_cache_t'(AXIWPREF``arcache),  \
					  npu_axi_prot_t'(AXIWPREF``arprot),    \
					  npu_axi_lock_t'(AXIWPREF``arlock),    \
					  npu_axi_burst_t'(AXIWPREF``arburst),  \
					  npu_axi_len_t'(AXIWPREF``arlen),      \
					  npu_axi_size_t'(AXIWPREF``arsize),    \
					  npu_axi_region_t'(AXIWPREF``arregion)}), // read command \
//.AXIPREF``ar.addr  ( AXIWPREF``araddr ),   // \
//.AXIPREF``ar.cache ( AXIWPREF``arcache  ), // \
//.AXIPREF``ar.prot  ( AXIWPREF``arprot   ), // \
//.AXIPREF``ar.lock  ( AXIWPREF``arlock   ), // \
//.AXIPREF``ar.burst ( AXIWPREF``arburst  ), // \
//.AXIPREF``ar.len   ( AXIWPREF``arlen    ), // \
//.AXIPREF``ar.size  ( AXIWPREF``arsize   ), // \
//.AXIPREF``ar.region( AXIWPREF``arregion), // \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid   ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready   ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid      ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata    ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp    ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser    ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast    ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid  ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready  ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid     ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser   ), // write command user field \
.AXIPREF``aw      ( {AXIWPREF``awaddr,AXIWPREF``awcache,AXIWPREF``awprot,AXIWPREF``awlock,AXIWPREF``awburst,AXIWPREF``awlen,AXIWPREF``awsize,AXIWPREF``awregion}), // write command \
//.AXIPREF``aw.addr  ( AXIWPREF``awaddr  ), // write command address \
//.AXIPREF``aw.cache ( AXIWPREF``awcache ), // \
//.AXIPREF``aw.prot  ( AXIWPREF``awprot  ), // \
//.AXIPREF``aw.lock  ( AXIWPREF``awlock  ), // \
//.AXIPREF``aw.burst ( AXIWPREF``awburst ), // \
//.AXIPREF``aw.len   ( AXIWPREF``awlen   ), // \
//.AXIPREF``aw.size  ( AXIWPREF``awsize  ), // \
//.AXIPREF``awregion( AXIWPREF``aw.region), // \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid   ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready   ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata    ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb    ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser    ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast    ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid   ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready   ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid      ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser    ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp    )  // write response \


//
// NPU AXI instance port assignment
//   Module instance has single AXI interface with flat logic ports connecting to the array
//   Connect one of the N interfaces in the array
//   Using packed structure types on the array side, flat on the module side
//
`define AXIINSTM_FLAT(M,AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid[M]  ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready[M]  ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid[M]     ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser[M]   ), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``ar[M].addr  ), // read address \
.AXIPREF``arcache ( AXIWPREF``ar[M].cache ), // \
.AXIPREF``arprot  ( AXIWPREF``ar[M].prot  ), // \
.AXIPREF``arlock  ( AXIWPREF``ar[M].lock  ), // \
.AXIPREF``arburst ( AXIWPREF``ar[M].burst ), // \
.AXIPREF``arlen   ( AXIWPREF``ar[M].len   ), // \
.AXIPREF``arsize  ( AXIWPREF``ar[M].size  ), // \
//.AXIPREF``arregion( AXIWPREF``ar[M].region), // \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid[M]  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready[M]  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid[M]     ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata[M]   ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp[M]   ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser[M]   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast[M]   ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid[M]  ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready[M]  ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid[M]     ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser[M]   ), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``aw[M].addr  ), // write address \
.AXIPREF``awcache ( AXIWPREF``aw[M].cache ), // \
.AXIPREF``awprot  ( AXIWPREF``aw[M].prot  ), // \
.AXIPREF``awlock  ( AXIWPREF``aw[M].lock  ), // \
.AXIPREF``awburst ( AXIWPREF``aw[M].burst ), // \
.AXIPREF``awlen   ( AXIWPREF``aw[M].len   ), // \
.AXIPREF``awsize  ( AXIWPREF``aw[M].size  ), // \
//.AXIPREF``awregion( AXIWPREF``aw[M].region), // \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid[M]  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready[M]  ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata[M]   ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb[M]   ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser[M]   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast[M]   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid[M]  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready[M]  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid[M]     ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser[M]   ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[M]   )  // write response \

// ----------------------------------------------------------------------------
// Assign macros
// ----------------------------------------------------------------------------

//
// 
//
`define AXIASGN(N,AXIPREF,AXIWPREF) \
// read command channel \
assign AXIPREF``arvalid[N] = AXIWPREF``arvalid;    // read command valid \
assign AXIWPREF``arready   = AXIPREF``arready[N];  // read command accept \
assign AXIPREF``arid[N]    = AXIWPREF``arid;       // read command ID \
assign AXIPREF``aruser[N]  = AXIWPREF``aruser;     // read command user field \
assign AXIPREF``ar[N]      = AXIWPREF``ar;         // read command \
// read data channel \
assign AXIWPREF``rvalid    = AXIPREF``rvalid[N];   // read data valid \
assign AXIPREF``rready[N]  = AXIWPREF``rready;     // read data accept \
assign AXIWPREF``rid       = AXIPREF``rid[N];      // read data id \
assign AXIWPREF``rdata     = AXIPREF``rdata[N];    // read data \
assign AXIWPREF``rresp     = AXIPREF``rresp[N];    // read response \
assign AXIWPREF``ruser     = AXIPREF``ruser[N];    // read data user field \
assign AXIWPREF``rlast     = AXIPREF``rlast[N];    // read last \
// write command channel \
assign AXIPREF``awvalid[N] = AXIWPREF``awvalid;    // write command valid \
assign AXIWPREF``awready   = AXIPREF``awready[N];  // write command accept \
assign AXIPREF``awid[N]    = AXIWPREF``awid;       // write command ID \
assign AXIPREF``awuser[N]  = AXIWPREF``awuser;     // write command user field \
assign AXIPREF``aw[N]      = AXIWPREF``aw;         // write command \
// write data channel \
assign AXIPREF``wvalid[N]  = AXIWPREF``wvalid;     // write data valid \
assign AXIWPREF``wready    = AXIPREF``wready[N];   // write data accept \
assign AXIPREF``wdata[N]   = AXIWPREF``wdata;      // write data \
assign AXIPREF``wstrb[N]   = AXIWPREF``wstrb;      // write data strobe \
assign AXIPREF``wuser[N]   = AXIWPREF``wuser;      // write data user field \
assign AXIPREF``wlast[N]   = AXIWPREF``wlast;      // write data last \
// write response channel \
assign AXIWPREF``bvalid    = AXIPREF``bvalid[N];   // write response valid \
assign AXIPREF``bready[N]  = AXIWPREF``bready;     // write response accept \
assign AXIWPREF``bid       = AXIPREF``bid[N];      // write response id \
assign AXIWPREF``buser     = AXIPREF``buser[N];    // read data user field \
assign AXIWPREF``bresp     = AXIPREF``bresp[N]     // write response \

//
//
//
`define AXIASGNNID(N,AXIPREF,AXIWPREF) \
// read command channel \
assign AXIPREF``arvalid[N] = AXIWPREF``arvalid;    // read command valid \
assign AXIWPREF``arready   = AXIPREF``arready[N];  // read command accept \
assign AXIPREF``arid[N]    = unsigned'(0);         // read command ID \
assign AXIPREF``aruser[N]  = AXIWPREF``aruser;     // read command user field \
assign AXIPREF``ar[N]      = AXIWPREF``ar;         // read command \
// read data channel \
assign AXIWPREF``rvalid    = AXIPREF``rvalid[N];   // read data valid \
assign AXIPREF``rready[N]  = AXIWPREF``rready;     // read data accept \
assign AXIWPREF``rid       = unsigned'(0);         // read data id \
assign AXIWPREF``rdata     = AXIPREF``rdata[N];    // read data \
assign AXIWPREF``rresp     = AXIPREF``rresp[N];    // read response \
assign AXIWPREF``ruser     = AXIPREF``ruser[N];    // read data user field \
assign AXIWPREF``rlast     = AXIPREF``rlast[N];    // read last \
// write command channel \
assign AXIPREF``awvalid[N] = AXIWPREF``awvalid;    // write command valid \
assign AXIWPREF``awready   = AXIPREF``awready[N];  // write command accept \
assign AXIPREF``awid[N]    = unsigned'(0);         // write command ID \
assign AXIPREF``awuser[N]  = AXIWPREF``awuser;     // write command user field \
assign AXIPREF``aw[N]      = AXIWPREF``aw;         // write command \
// write data channel \
assign AXIPREF``wvalid[N]  = AXIWPREF``wvalid;     // write data valid \
assign AXIWPREF``wready    = AXIPREF``wready[N];   // write data accept \
assign AXIPREF``wdata[N]   = AXIWPREF``wdata;      // write data \
assign AXIPREF``wstrb[N]   = AXIWPREF``wstrb;      // write data strobe \
assign AXIPREF``wuser[N]   = AXIWPREF``wuser;      // write data user field \
assign AXIPREF``wlast[N]   = AXIWPREF``wlast;      // write data last \
// write response channel \
assign AXIWPREF``bvalid    = AXIPREF``bvalid[N];   // write response valid \
assign AXIPREF``bready[N]  = AXIWPREF``bready;     // write response accept \
assign AXIWPREF``bid       = unsigned'(0);         // write response id \
assign AXIWPREF``buser     = AXIPREF``buser[N];    // read data user field \
assign AXIWPREF``bresp     = AXIPREF``bresp[N]     // write response \

//
//
//
`define AXIASGNEID(N,AXIPREF,AXIWPREF,X,Y) \
// read command channel \
assign AXIPREF``arvalid[N] = AXIWPREF``arvalid;    // read command valid \
assign AXIWPREF``arready   = AXIPREF``arready[N];  // read command accept \
assign AXIPREF``arid[N]    = {{(X-Y){1'b0}},AXIWPREF``arid};         // read command ID \
assign AXIPREF``aruser[N]  = AXIWPREF``aruser;     // read command user field \
assign AXIPREF``ar[N]      = AXIWPREF``ar;         // read command \
// read data channel \
assign AXIWPREF``rvalid    = AXIPREF``rvalid[N];   // read data valid \
assign AXIPREF``rready[N]  = AXIWPREF``rready;     // read data accept \
assign AXIWPREF``rid       = AXIPREF``rid[N][0+:Y];// read data id \
assign AXIWPREF``rdata     = AXIPREF``rdata[N];    // read data \
assign AXIWPREF``rresp     = AXIPREF``rresp[N];    // read response \
assign AXIWPREF``ruser     = AXIPREF``ruser[N];    // read data user field \
assign AXIWPREF``rlast     = AXIPREF``rlast[N];    // read last \
// write command channel \
assign AXIPREF``awvalid[N] = AXIWPREF``awvalid;    // write command valid \
assign AXIWPREF``awready   = AXIPREF``awready[N];  // write command accept \
assign AXIPREF``awid[N]    = {{(X-Y){1'b0}},AXIWPREF``awid};         // write command ID \
assign AXIPREF``awuser[N]  = AXIWPREF``awuser;     // write command user field \
assign AXIPREF``aw[N]      = AXIWPREF``aw;         // write command \
// write data channel \
assign AXIPREF``wvalid[N]  = AXIWPREF``wvalid;     // write data valid \
assign AXIWPREF``wready    = AXIPREF``wready[N];   // write data accept \
assign AXIPREF``wdata[N]   = AXIWPREF``wdata;      // write data \
assign AXIPREF``wstrb[N]   = AXIWPREF``wstrb;      // write data strobe \
assign AXIPREF``wuser[N]   = AXIWPREF``wuser;      // write data user field \
assign AXIPREF``wlast[N]   = AXIWPREF``wlast;      // write data last \
// write response channel \
assign AXIWPREF``bvalid    = AXIPREF``bvalid[N];   // write response valid \
assign AXIPREF``bready[N]  = AXIWPREF``bready;     // write response accept \
assign AXIWPREF``bid       = AXIPREF``bid[N][0+:Y];         // write response id \
assign AXIWPREF``buser     = AXIPREF``buser[N];    // read data user field \
assign AXIWPREF``bresp     = AXIPREF``bresp[N]     // write response \

//
//
//
`define AXIASGM(M,AXIWPREF,AXIPREF) \
// read command channel \
assign AXIPREF``arvalid     = AXIWPREF``arvalid[M]; // read command valid \
assign AXIWPREF``arready[M] = AXIPREF``arready;     // read command accept \
assign AXIPREF``arid        = AXIWPREF``arid[M];    // read command ID \
assign AXIPREF``aruser      = AXIWPREF``aruser[M];  // read command user field \
assign AXIPREF``ar          = AXIWPREF``ar[M];      // read command \
// read data channel \
assign AXIWPREF``rvalid[M]  = AXIPREF``rvalid;      // read data valid \
assign AXIPREF``rready      = AXIWPREF``rready[M];  // read data accept \
assign AXIWPREF``rid[M]     = AXIPREF``rid;         // read data id \
assign AXIWPREF``rdata[M]   = AXIPREF``rdata;       // read data \
assign AXIWPREF``rresp[M]   = AXIPREF``rresp;       // read response \
assign AXIWPREF``ruser[M]   = AXIPREF``ruser;       // read data user field \
assign AXIWPREF``rlast[M]   = AXIPREF``rlast;       // read last \
// write command channel \
assign AXIPREF``awvalid     = AXIWPREF``awvalid[M]; // write command valid \
assign AXIWPREF``awready[M] = AXIPREF``awready;     // write command accept \
assign AXIPREF``awid        = AXIWPREF``awid[M];    // write command ID \
assign AXIPREF``awuser      = AXIWPREF``awuser[M];  // write command user field \
assign AXIPREF``aw          = AXIWPREF``aw[M];      // write command \
// write data channel \
assign AXIPREF``wvalid      = AXIWPREF``wvalid[M];  // write data valid \
assign AXIWPREF``wready[M]  = AXIPREF``wready;      // write data accept \
assign AXIPREF``wdata       = AXIWPREF``wdata[M];   // write data \
assign AXIPREF``wstrb       = AXIWPREF``wstrb[M];   // write data strobe \
assign AXIPREF``wuser       = AXIWPREF``wuser[M];   // write data user field \
assign AXIPREF``wlast       = AXIWPREF``wlast[M];   // write data last \
// write response channel \
assign AXIWPREF``bvalid[M]  = AXIPREF``bvalid;      // write response valid \
assign AXIPREF``bready      = AXIWPREF``bready[M];  // write response accept \
assign AXIWPREF``bid[M]     = AXIPREF``bid;         // write response id \
assign AXIWPREF``buser[M]   = AXIPREF``buser;       // read data user field \
assign AXIWPREF``bresp[M]   = AXIPREF``bresp        // write response \

//
//
//
`define AXIASGMNID(M,AXIWPREF,AXIPREF) \
// read command channel \
assign AXIPREF``arvalid     = AXIWPREF``arvalid[M]; // read command valid \
assign AXIWPREF``arready[M] = AXIPREF``arready;     // read command accept \
assign AXIPREF``aruser      = AXIWPREF``aruser[M];  // read command user field \
assign AXIPREF``ar          = AXIWPREF``ar[M];      // read command \
// read data channel \
assign AXIWPREF``rvalid[M]  = AXIPREF``rvalid;      // read data valid \
assign AXIPREF``rready      = AXIWPREF``rready[M];  // read data accept \
assign AXIWPREF``rdata[M]   = AXIPREF``rdata;       // read data \
assign AXIWPREF``rresp[M]   = AXIPREF``rresp;       // read response \
assign AXIWPREF``ruser[M]   = AXIPREF``ruser;       // read data user field \
assign AXIWPREF``rlast[M]   = AXIPREF``rlast;       // read last \
// write command channel \
assign AXIPREF``awvalid     = AXIWPREF``awvalid[M]; // write command valid \
assign AXIWPREF``awready[M] = AXIPREF``awready;     // write command accept \
assign AXIPREF``awuser      = AXIWPREF``awuser[M];  // write command user field \
assign AXIPREF``aw          = AXIWPREF``aw[M];      // write command \
// write data channel \
assign AXIPREF``wvalid      = AXIWPREF``wvalid[M];  // write data valid \
assign AXIWPREF``wready[M]  = AXIPREF``wready;      // write data accept \
assign AXIPREF``wdata       = AXIWPREF``wdata[M];   // write data \
assign AXIPREF``wstrb       = AXIWPREF``wstrb[M];   // write data strobe \
assign AXIPREF``wuser       = AXIWPREF``wuser[M];   // write data user field \
assign AXIPREF``wlast       = AXIWPREF``wlast[M];   // write data last \
// write response channel \
assign AXIWPREF``bvalid[M]  = AXIPREF``bvalid;      // write response valid \
assign AXIPREF``bready      = AXIWPREF``bready[M];  // write response accept \
assign AXIWPREF``buser[M]   = AXIPREF``buser;       // read data user field \
assign AXIWPREF``bresp[M]   = AXIPREF``bresp        // write response \

//
//
//
`define AXIASGNM(AXIPREF,N,AXIWPREF,M) \
// read command channel \
assign AXIPREF``arvalid[N]  = AXIWPREF``arvalid[M]; // read command valid \
assign AXIWPREF``arready[M] = AXIPREF``arready[N];     // read command accept \
assign AXIPREF``arid[N]     = AXIWPREF``arid[M];    // read command ID \
assign AXIPREF``aruser[N]   = AXIWPREF``aruser[M];  // read command user field \
assign AXIPREF``ar[N]       = AXIWPREF``ar[M];      // read command \
// read data channel \
assign AXIWPREF``rvalid[M]  = AXIPREF``rvalid[N];      // read data valid \
assign AXIPREF``rready[N]   = AXIWPREF``rready[M];  // read data accept \
assign AXIWPREF``rid[M]     = AXIPREF``rid[N];         // read data id \
assign AXIWPREF``rdata[M]   = AXIPREF``rdata[N];       // read data \
assign AXIWPREF``rresp[M]   = AXIPREF``rresp[N];       // read response \
assign AXIWPREF``ruser[M]   = AXIPREF``ruser[N];       // read data user field \
assign AXIWPREF``rlast[M]   = AXIPREF``rlast[N];       // read last \
// write command channel \
assign AXIPREF``awvalid[N]  = AXIWPREF``awvalid[M]; // write command valid \
assign AXIWPREF``awready[M] = AXIPREF``awready[N];  // write command accept \
assign AXIPREF``awid[N]     = AXIWPREF``awid[M];    // write command ID \
assign AXIPREF``awuser[N]   = AXIWPREF``awuser[M];  // write command user field \
assign AXIPREF``aw[N]       = AXIWPREF``aw[M];      // write command \
// write data channel \
assign AXIPREF``wvalid[N]   = AXIWPREF``wvalid[M];  // write data valid \
assign AXIWPREF``wready[M]  = AXIPREF``wready[N];      // write data accept \
assign AXIPREF``wdata[N]    = AXIWPREF``wdata[M];   // write data \
assign AXIPREF``wstrb[N]    = AXIWPREF``wstrb[M];   // write data strobe \
assign AXIPREF``wuser[N]    = AXIWPREF``wuser[M];   // write data user field \
assign AXIPREF``wlast[N]    = AXIWPREF``wlast[M];   // write data last \
// write response channel \
assign AXIWPREF``bvalid[M]  = AXIPREF``bvalid[N];      // write response valid \
assign AXIPREF``bready[N]   = AXIWPREF``bready[M];  // write response accept \
assign AXIWPREF``bid[M]     = AXIPREF``bid[N];         // write response id \
assign AXIWPREF``buser[M]   = AXIPREF``buser[N];       // read data user field \
assign AXIWPREF``bresp[M]   = AXIPREF``bresp[N]        // write response \

//
//
//
`define AXIWASG(AXIWPREF,AXIPREF) \
// write command channel \
assign AXIPREF``awvalid  = AXIWPREF``awvalid; // write command valid \
assign AXIWPREF``awready = AXIPREF``awready;     // write command accept \
assign AXIPREF``awid     = AXIWPREF``awid;    // write command ID \
assign AXIPREF``awuser   = AXIWPREF``awuser;  // write command user field \
assign AXIPREF``aw       = AXIWPREF``aw;      // write command \
// write data channel \
assign AXIPREF``wvalid   = AXIWPREF``wvalid;  // write data valid \
assign AXIWPREF``wready  = AXIPREF``wready;      // write data accept \
assign AXIPREF``wdata    = AXIWPREF``wdata;   // write data \
assign AXIPREF``wstrb    = AXIWPREF``wstrb;   // write data strobe \
assign AXIPREF``wuser    = AXIWPREF``wuser;   // write data user field \
assign AXIPREF``wlast    = AXIWPREF``wlast;   // write data last \
// write response channel \
assign AXIWPREF``bvalid  = AXIPREF``bvalid;      // write response valid \
assign AXIPREF``bready   = AXIWPREF``bready;  // write response accept \
assign AXIWPREF``bid     = AXIPREF``bid;         // write response id \
assign AXIWPREF``buser   = AXIPREF``buser;       // read data user field \
assign AXIWPREF``bresp   = AXIPREF``bresp        // write response \

//
//
//
`define AXIASGNANU(AXIWPREF,AXIPREF) \
// read command channel \
assign AXIPREF``arvalid  = AXIWPREF``arvalid; // read command valid \
assign AXIWPREF``arready = AXIPREF``arready;     // read command accept \
assign AXIPREF``arid     = AXIWPREF``arid;    // read command ID \
// read data channel \
assign AXIWPREF``rvalid  = AXIPREF``rvalid;      // read data valid \
assign AXIPREF``rready   = AXIWPREF``rready;  // read data accept \
assign AXIWPREF``rid     = AXIPREF``rid;         // read data id \
assign AXIWPREF``rdata   = AXIPREF``rdata;       // read data \
assign AXIWPREF``rresp   = AXIPREF``rresp;       // read response \
assign AXIWPREF``ruser   = AXIPREF``ruser;       // read data user field \
assign AXIWPREF``rlast   = AXIPREF``rlast;       // read last \
// write command channel \
assign AXIPREF``awvalid  = AXIWPREF``awvalid; // write command valid \
assign AXIWPREF``awready = AXIPREF``awready;     // write command accept \
assign AXIPREF``awid     = AXIWPREF``awid;    // write command ID \
// write data channel \
assign AXIPREF``wvalid   = AXIWPREF``wvalid;  // write data valid \
assign AXIWPREF``wready  = AXIPREF``wready;      // write data accept \
assign AXIPREF``wdata    = AXIWPREF``wdata;   // write data \
assign AXIPREF``wstrb    = AXIWPREF``wstrb;   // write data strobe \
assign AXIPREF``wuser    = AXIWPREF``wuser;   // write data user field \
assign AXIPREF``wlast    = AXIWPREF``wlast;   // write data last \
// write response channel \
assign AXIWPREF``bvalid  = AXIPREF``bvalid;      // write response valid \
assign AXIPREF``bready   = AXIWPREF``bready;  // write response accept \
assign AXIWPREF``bid     = AXIPREF``bid;         // write response id \
assign AXIWPREF``buser   = AXIPREF``buser;       // read data user field \
assign AXIWPREF``bresp   = AXIPREF``bresp        // write response \

//
//
//
`define AXIASG(AXIWPREF,AXIPREF) \
// read command channel \
assign AXIPREF``arvalid  = AXIWPREF``arvalid; // read command valid \
assign AXIWPREF``arready = AXIPREF``arready;     // read command accept \
assign AXIPREF``arid     = AXIWPREF``arid;    // read command ID \
assign AXIPREF``aruser   = AXIWPREF``aruser;  // read command user field \
assign AXIPREF``ar       = AXIWPREF``ar;      // read command \
// read data channel \
assign AXIWPREF``rvalid  = AXIPREF``rvalid;      // read data valid \
assign AXIPREF``rready   = AXIWPREF``rready;  // read data accept \
assign AXIWPREF``rid     = AXIPREF``rid;         // read data id \
assign AXIWPREF``rdata   = AXIPREF``rdata;       // read data \
assign AXIWPREF``rresp   = AXIPREF``rresp;       // read response \
assign AXIWPREF``ruser   = AXIPREF``ruser;       // read data user field \
assign AXIWPREF``rlast   = AXIPREF``rlast;       // read last \
// write command channel \
assign AXIPREF``awvalid  = AXIWPREF``awvalid; // write command valid \
assign AXIWPREF``awready = AXIPREF``awready;     // write command accept \
assign AXIPREF``awid     = AXIWPREF``awid;    // write command ID \
assign AXIPREF``awuser   = AXIWPREF``awuser;  // write command user field \
assign AXIPREF``aw       = AXIWPREF``aw;      // write command \
// write data channel \
assign AXIPREF``wvalid   = AXIWPREF``wvalid;  // write data valid \
assign AXIWPREF``wready  = AXIPREF``wready;      // write data accept \
assign AXIPREF``wdata    = AXIWPREF``wdata;   // write data \
assign AXIPREF``wstrb    = AXIWPREF``wstrb;   // write data strobe \
assign AXIPREF``wuser    = AXIWPREF``wuser;   // write data user field \
assign AXIPREF``wlast    = AXIWPREF``wlast;   // write data last \
// write response channel \
assign AXIWPREF``bvalid  = AXIPREF``bvalid;      // write response valid \
assign AXIPREF``bready   = AXIWPREF``bready;  // write response accept \
assign AXIWPREF``bid     = AXIPREF``bid;         // write response id \
assign AXIWPREF``buser   = AXIPREF``buser;       // read data user field \
assign AXIWPREF``bresp   = AXIPREF``bresp        // write response \

//
//
//
`define AXIASGNID(AXIWPREF,AXIPREF) \
// read command channel \
assign AXIPREF``arvalid  = AXIWPREF``arvalid; // read command valid \
assign AXIWPREF``arready = AXIPREF``arready;     // read command accept \
assign AXIPREF``aruser   = AXIWPREF``aruser;  // read command user field \
assign AXIPREF``ar       = AXIWPREF``ar;      // read command \
// read data channel \
assign AXIWPREF``rvalid  = AXIPREF``rvalid;      // read data valid \
assign AXIPREF``rready   = AXIWPREF``rready;  // read data accept \
assign AXIWPREF``rdata   = AXIPREF``rdata;       // read data \
assign AXIWPREF``rresp   = AXIPREF``rresp;       // read response \
assign AXIWPREF``ruser   = AXIPREF``ruser;       // read data user field \
assign AXIWPREF``rlast   = AXIPREF``rlast;       // read last \
// write command channel \
assign AXIPREF``awvalid  = AXIWPREF``awvalid; // write command valid \
assign AXIWPREF``awready = AXIPREF``awready;     // write command accept \
assign AXIPREF``awuser   = AXIWPREF``awuser;  // write command user field \
assign AXIPREF``aw       = AXIWPREF``aw;      // write command \
// write data channel \
assign AXIPREF``wvalid   = AXIWPREF``wvalid;  // write data valid \
assign AXIWPREF``wready  = AXIPREF``wready;      // write data accept \
assign AXIPREF``wdata    = AXIWPREF``wdata;   // write data \
assign AXIPREF``wstrb    = AXIWPREF``wstrb;   // write data strobe \
assign AXIPREF``wuser    = AXIWPREF``wuser;   // write data user field \
assign AXIPREF``wlast    = AXIWPREF``wlast;   // write data last \
// write response channel \
assign AXIWPREF``bvalid  = AXIPREF``bvalid;      // write response valid \
assign AXIPREF``bready   = AXIWPREF``bready;  // write response accept \
assign AXIWPREF``buser   = AXIPREF``buser;       // read data user field \
assign AXIWPREF``bresp   = AXIPREF``bresp        // write response \

//
//
//
`define AXIASG_EXT(AXIWPREF,AXIPREF) \
assign AXIWPREF``arvalid   = AXIPREF``arvalid; \
assign AXIPREF``arready   = AXIWPREF``arready; \
assign AXIWPREF``arid      = AXIPREF``arid; \
assign AXIWPREF``aruser    = AXIPREF``aruser; \
assign AXIWPREF``ar.addr   = AXIPREF``araddr; \
assign AXIWPREF``ar.cache  = AXIPREF``arcache; \
assign AXIWPREF``ar.prot   = AXIPREF``arprot; \
assign AXIWPREF``ar.lock   = npu_axi_lock_t'(AXIPREF``arlock); \
assign AXIWPREF``ar.burst  = npu_axi_burst_t'(AXIPREF``arburst); \
assign AXIWPREF``ar.len    = AXIPREF``arlen; \
assign AXIWPREF``ar.size   = AXIPREF``arsize; \
assign AXIWPREF``ar.region = '0; \
assign AXIPREF``rvalid     = AXIWPREF``rvalid; \
assign AXIWPREF``rready    = AXIPREF``rready; \
assign AXIPREF``rid        = AXIWPREF``rid; \
assign AXIPREF``rdata      = AXIWPREF``rdata; \
assign AXIPREF``rresp      = AXIWPREF``rresp; \
assign AXIPREF``ruser      = AXIWPREF``ruser; \
assign AXIPREF``rlast      = AXIWPREF``rlast; \
assign AXIWPREF``awvalid   = AXIPREF``awvalid; \
assign AXIPREF``awready    = AXIWPREF``awready; \
assign AXIWPREF``awid      = AXIPREF``awid; \
assign AXIWPREF``awuser    = AXIPREF``awuser; \
assign AXIWPREF``aw.addr   = AXIPREF``awaddr; \
assign AXIWPREF``aw.cache  = AXIPREF``awcache; \
assign AXIWPREF``aw.prot   = AXIPREF``awprot; \
assign AXIWPREF``aw.lock   = npu_axi_lock_t'(AXIPREF``awlock); \
assign AXIWPREF``aw.burst  = npu_axi_burst_t'(AXIPREF``awburst); \
assign AXIWPREF``aw.len    = AXIPREF``awlen; \
assign AXIWPREF``aw.size   = AXIPREF``awsize; \
assign AXIWPREF``aw.region = '0; \
assign AXIWPREF``wvalid    = AXIPREF``wvalid; \
assign AXIPREF``wready     = AXIWPREF``wready; \
assign AXIWPREF``wdata     = AXIPREF``wdata; \
assign AXIWPREF``wstrb     = AXIPREF``wstrb; \
assign AXIWPREF``wuser     = AXIPREF``wuser; \
assign AXIWPREF``wlast     = AXIPREF``wlast; \
assign AXIPREF``bvalid     = AXIWPREF``bvalid; \
assign AXIWPREF``bready    = AXIPREF``bready; \
assign AXIPREF``bid        = AXIWPREF``bid; \
assign AXIPREF``buser      = AXIWPREF``buser; \
assign AXIPREF``bresp      = AXIWPREF``bresp

//
//
//
`define AXIASGM_EXT(M,AXIPREF,AXIWPREF) \
assign AXIPREF``arvalid     = AXIWPREF``arvalid[M]; \
assign AXIWPREF``arready[M] = AXIPREF``arready; \
assign AXIPREF``arid        = AXIWPREF``arid[M]; \
assign AXIPREF``aruser      = AXIWPREF``aruser[M]; \
assign AXIPREF``araddr      = AXIWPREF``ar[M].addr; \
assign AXIPREF``arcache     = AXIWPREF``ar[M].cache; \
assign AXIPREF``arprot      = AXIWPREF``ar[M].prot; \
assign AXIPREF``arlock      = AXIWPREF``ar[M].lock; \
assign AXIPREF``arburst     = AXIWPREF``ar[M].burst; \
assign AXIPREF``arlen       = AXIWPREF``ar[M].len; \
assign AXIPREF``arsize      = AXIWPREF``ar[M].size; \
assign AXIPREF``arregion    = AXIWPREF``ar[M].region; \
assign AXIWPREF``rvalid[M]  = AXIPREF``rvalid; \
assign AXIPREF``rready      = AXIWPREF``rready[M]; \
assign AXIWPREF``rid[M]     = AXIPREF``rid; \
assign AXIWPREF``rdata[M]   = AXIPREF``rdata; \
assign AXIWPREF``rresp[M]   = npu_axi_resp_t'(AXIPREF``rresp); \
assign AXIWPREF``ruser[M]   = AXIPREF``ruser; \
assign AXIWPREF``rlast[M]   = AXIPREF``rlast; \
assign AXIPREF``awvalid     = AXIWPREF``awvalid[M]; \
assign AXIWPREF``awready[M] = AXIPREF``awready; \
assign AXIPREF``awid        = AXIWPREF``awid[M]; \
assign AXIPREF``awuser      = AXIWPREF``awuser[M]; \
assign AXIPREF``awaddr      = AXIWPREF``aw[M].addr; \
assign AXIPREF``awcache     = AXIWPREF``aw[M].cache; \
assign AXIPREF``awprot      = AXIWPREF``aw[M].prot; \
assign AXIPREF``awlock      = AXIWPREF``aw[M].lock; \
assign AXIPREF``awburst     = AXIWPREF``aw[M].burst; \
assign AXIPREF``awlen       = AXIWPREF``aw[M].len; \
assign AXIPREF``awsize      = AXIWPREF``aw[M].size; \
assign AXIPREF``awregion    = AXIWPREF``aw[M].region; \
assign AXIPREF``wvalid      = AXIWPREF``wvalid[M]; \
assign AXIWPREF``wready[M]  = AXIPREF``wready; \
assign AXIPREF``wdata       = AXIWPREF``wdata[M]; \
assign AXIPREF``wstrb       = AXIWPREF``wstrb[M]; \
assign AXIPREF``wuser       = AXIWPREF``wuser[M]; \
assign AXIPREF``wlast       = AXIWPREF``wlast[M]; \
assign AXIWPREF``bvalid[M]  = AXIPREF``bvalid; \
assign AXIPREF``bready      = AXIWPREF``bready[M]; \
assign AXIWPREF``bid[M]     = AXIPREF``bid; \
assign AXIWPREF``buser[M]   = AXIPREF``buser; \
assign AXIWPREF``bresp[M]   = npu_axi_resp_t'(AXIPREF``bresp)

//
//
//
`define AXIASGS_EXT(AXIPREF,AXIWPREF) \
assign AXIPREF``arvalid     = AXIWPREF``arvalid; \
assign AXIWPREF``arready    = AXIPREF``arready; \
assign AXIPREF``arid        = AXIWPREF``arid; \
assign AXIPREF``aruser      = AXIWPREF``aruser; \
assign AXIPREF``araddr      = AXIWPREF``ar.addr; \
assign AXIPREF``arcache     = AXIWPREF``ar.cache; \
assign AXIPREF``arprot      = AXIWPREF``ar.prot; \
assign AXIPREF``arlock      = AXIWPREF``ar.lock; \
assign AXIPREF``arburst     = AXIWPREF``ar.burst; \
assign AXIPREF``arlen       = AXIWPREF``ar.len; \
assign AXIPREF``arsize      = AXIWPREF``ar.size; \
assign AXIPREF``arregion    = AXIWPREF``ar.region; \
assign AXIWPREF``rvalid     = AXIPREF``rvalid; \
assign AXIPREF``rready      = AXIWPREF``rready; \
assign AXIWPREF``rid        = AXIPREF``rid; \
assign AXIWPREF``rdata      = AXIPREF``rdata; \
assign AXIWPREF``rresp      = npu_axi_resp_t'(AXIPREF``rresp); \
assign AXIWPREF``ruser      = AXIPREF``ruser; \
assign AXIWPREF``rlast      = AXIPREF``rlast; \
assign AXIPREF``awvalid     = AXIWPREF``awvalid; \
assign AXIWPREF``awready    = AXIPREF``awready; \
assign AXIPREF``awid        = AXIWPREF``awid; \
assign AXIPREF``awuser      = AXIWPREF``awuser; \
assign AXIPREF``awaddr      = AXIWPREF``aw.addr; \
assign AXIPREF``awcache     = AXIWPREF``aw.cache; \
assign AXIPREF``awprot      = AXIWPREF``aw.prot; \
assign AXIPREF``awlock      = AXIWPREF``aw.lock; \
assign AXIPREF``awburst     = AXIWPREF``aw.burst; \
assign AXIPREF``awlen       = AXIWPREF``aw.len; \
assign AXIPREF``awsize      = AXIWPREF``aw.size; \
assign AXIPREF``awregion    = AXIWPREF``aw.region; \
assign AXIPREF``wvalid      = AXIWPREF``wvalid; \
assign AXIWPREF``wready     = AXIPREF``wready; \
assign AXIPREF``wdata       = AXIWPREF``wdata; \
assign AXIPREF``wstrb       = AXIWPREF``wstrb; \
assign AXIPREF``wuser       = AXIWPREF``wuser; \
assign AXIPREF``wlast       = AXIWPREF``wlast; \
assign AXIWPREF``bvalid     = AXIPREF``bvalid; \
assign AXIPREF``bready      = AXIWPREF``bready; \
assign AXIWPREF``bid        = AXIPREF``bid; \
assign AXIWPREF``buser      = AXIPREF``buser; \
assign AXIWPREF``bresp      = npu_axi_resp_t'(AXIPREF``bresp)
//
//
//
`define AXIASGN_EXT(M,AXIWPREF,AXIPREF) \
assign AXIWPREF``arvalid[M]   =  AXIPREF``arvalid; \
assign AXIPREF``arready       =  AXIWPREF``arready[M]; \
assign AXIWPREF``arid[M]      =  AXIPREF``arid; \
assign AXIWPREF``aruser[M]    =  AXIPREF``aruser; \
assign AXIWPREF``ar[M].addr   =  AXIPREF``araddr; \
assign AXIWPREF``ar[M].cache  =  AXIPREF``arcache; \
assign AXIWPREF``ar[M].prot   =  AXIPREF``arprot; \
assign AXIWPREF``ar[M].lock   =  npu_axi_lock_t'(AXIPREF``arlock); \
assign AXIWPREF``ar[M].burst  =  npu_axi_burst_t'(AXIPREF``arburst); \
assign AXIWPREF``ar[M].len    =  AXIPREF``arlen; \
assign AXIWPREF``ar[M].size   =  AXIPREF``arsize; \
assign AXIWPREF``ar[M].region =  AXIPREF``arregion; \
assign AXIPREF``rvalid        =  AXIWPREF``rvalid[M]; \
assign AXIWPREF``rready[M]    =  AXIPREF``rready; \
assign AXIPREF``rid           =  AXIWPREF``rid[M]; \
assign AXIPREF``rdata         =  AXIWPREF``rdata[M]; \
assign AXIPREF``rresp         =  AXIWPREF``rresp[M]; \
assign AXIPREF``ruser         =  AXIWPREF``ruser[M]; \
assign AXIPREF``rlast         =  AXIWPREF``rlast[M]; \
assign AXIWPREF``awvalid[M]   =  AXIPREF``awvalid; \
assign AXIPREF``awready       =  AXIWPREF``awready[M]; \
assign AXIWPREF``awid[M]      =  AXIPREF``awid; \
assign AXIWPREF``awuser[M]    =  AXIPREF``awuser; \
assign AXIWPREF``aw[M].addr   =  AXIPREF``awaddr; \
assign AXIWPREF``aw[M].cache  =  AXIPREF``awcache; \
assign AXIWPREF``aw[M].prot   =  AXIPREF``awprot; \
assign AXIWPREF``aw[M].lock   =  npu_axi_lock_t'(AXIPREF``awlock); \
assign AXIWPREF``aw[M].burst  =  npu_axi_burst_t'(AXIPREF``awburst); \
assign AXIWPREF``aw[M].len    =  AXIPREF``awlen; \
assign AXIWPREF``aw[M].size   =  AXIPREF``awsize; \
assign AXIWPREF``aw[M].region =  AXIPREF``awregion; \
assign AXIWPREF``wvalid[M]    =  AXIPREF``wvalid; \
assign AXIPREF``wready        =  AXIWPREF``wready[M]; \
assign AXIWPREF``wdata[M]     =  AXIPREF``wdata; \
assign AXIWPREF``wstrb[M]     =  AXIPREF``wstrb; \
assign AXIWPREF``wuser[M]     =  AXIPREF``wuser; \
assign AXIWPREF``wlast[M]     =  AXIPREF``wlast; \
assign AXIPREF``bvalid        =  AXIWPREF``bvalid[M]; \
assign AXIWPREF``bready[M]    =  AXIPREF``bready; \
assign AXIPREF``bid           =  AXIWPREF``bid[M]; \
assign AXIPREF``buser         =  AXIWPREF``buser[M]; \
assign AXIPREF``bresp         =  AXIWPREF``bresp[M]


// ----------------------------------------------------------------------------
// Port declaration
// ----------------------------------------------------------------------------

//
// AXI master interface port on NPU module
//
`define AXIMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic                        AXIPREF``arvalid, // read command valid \
input  logic                        AXIPREF``arready, // read command accept \
output logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_cmd_t                AXIPREF``ar,      // read command \
// read data channel \
input  logic                        AXIPREF``rvalid,  // read data valid \
output logic                        AXIPREF``rready,  // read data accept \
input  logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
input  npu_axi_resp_t               AXIPREF``rresp,   // read response \
input  logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic                        AXIPREF``rlast,   // read last \
// write command channel \
output logic                        AXIPREF``awvalid, // write command valid \
input  logic                        AXIPREF``awready, // write command accept \
output logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_cmd_t                AXIPREF``aw,      // write command \
// write data channel \
output logic                        AXIPREF``wvalid,  // write data valid \
input  logic                        AXIPREF``wready,  // write data accept \
output logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
output logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
output logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic                        AXIPREF``wlast,   // write data last \
// write response channel \
input  logic                        AXIPREF``bvalid,  // write response valid \
output logic                        AXIPREF``bready,  // write response accept \
input  logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t               AXIPREF``bresp    // write response \

//
// AXI master interface port on NPU module
//
`define AXINODATAMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic                        AXIPREF``arvalid, // read command valid \
input  logic                        AXIPREF``arready, // read command accept \
output logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_cmd_t                AXIPREF``ar,      // read command \
// read data channel \
input  logic                        AXIPREF``rvalid,  // read data valid \
output logic                        AXIPREF``rready,  // read data accept \
input  logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  npu_axi_resp_t               AXIPREF``rresp,   // read response \
input  logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic                        AXIPREF``rlast,   // read last \
// write command channel \
output logic                        AXIPREF``awvalid, // write command valid \
input  logic                        AXIPREF``awready, // write command accept \
output logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_cmd_t                AXIPREF``aw,      // write command \
// write data channel \
output logic                        AXIPREF``wvalid,  // write data valid \
input  logic                        AXIPREF``wready,  // write data accept \
output logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic                        AXIPREF``wlast,   // write data last \
// write response channel \
input  logic                        AXIPREF``bvalid,  // write response valid \
output logic                        AXIPREF``bready,  // write response accept \
input  logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t               AXIPREF``bresp    // write response \

//
//
//
`define AXIMSTN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic          [N-1:0]              AXIPREF``arvalid, // read command valid \
input  logic          [N-1:0]              AXIPREF``arready, // read command accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_cmd_t  [N-1:0]              AXIPREF``ar,      // read command \
// read data channel \
input  logic          [N-1:0]              AXIPREF``rvalid,  // read data valid \
output logic          [N-1:0]              AXIPREF``rready,  // read data accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  logic          [N-1:0][AXIDW-1:0]   AXIPREF``rdata,   // read data \
input  npu_axi_resp_t [N-1:0]              AXIPREF``rresp,   // read response \
input  logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic          [N-1:0]              AXIPREF``rlast,   // read last \
// write command channel \
output logic          [N-1:0]              AXIPREF``awvalid, // write command valid \
input  logic          [N-1:0]              AXIPREF``awready, // write command accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_cmd_t  [N-1:0]              AXIPREF``aw,      // write command \
// write data channel \
output logic          [N-1:0]              AXIPREF``wvalid,  // write data valid \
input  logic          [N-1:0]              AXIPREF``wready,  // write data accept \
output logic          [N-1:0][AXIDW-1:0]   AXIPREF``wdata,   // write data \
output logic          [N-1:0][AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
output logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic          [N-1:0]              AXIPREF``wlast,   // write data last \
// write response channel \
input  logic          [N-1:0]              AXIPREF``bvalid,  // write response valid \
output logic          [N-1:0]              AXIPREF``bready,  // write response accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \

//
//
//
`define AXINODATAMSTN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic          [N-1:0]              AXIPREF``arvalid, // read command valid \
input  logic          [N-1:0]              AXIPREF``arready, // read command accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_cmd_t  [N-1:0]              AXIPREF``ar,      // read command \
// read data channel \
input  logic          [N-1:0]              AXIPREF``rvalid,  // read data valid \
output logic          [N-1:0]              AXIPREF``rready,  // read data accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  npu_axi_resp_t [N-1:0]              AXIPREF``rresp,   // read response \
input  logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic          [N-1:0]              AXIPREF``rlast,   // read last \
// write command channel \
output logic          [N-1:0]              AXIPREF``awvalid, // write command valid \
input  logic          [N-1:0]              AXIPREF``awready, // write command accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_cmd_t  [N-1:0]              AXIPREF``aw,      // write command \
// write data channel \
output logic          [N-1:0]              AXIPREF``wvalid,  // write data valid \
input  logic          [N-1:0]              AXIPREF``wready,  // write data accept \
output logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic          [N-1:0]              AXIPREF``wlast,   // write data last \
// write response channel \
input  logic          [N-1:0]              AXIPREF``bvalid,  // write response valid \
output logic          [N-1:0]              AXIPREF``bready,  // write response accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \


//
//
//
`define AXIMST_EXT(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic                        AXIPREF``arvalid, // read command valid \
input  logic                        AXIPREF``arready, // read command accept \
output logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_addr_t               AXIPREF``araddr,  // \
output npu_axi_cache_t              AXIPREF``arcache, // \
output npu_axi_prot_t               AXIPREF``arprot,  // \
output npu_axi_lock_t               AXIPREF``arlock,  // \
output npu_axi_burst_t              AXIPREF``arburst, // \
output npu_axi_len_t                AXIPREF``arlen,   // \
output npu_axi_size_t               AXIPREF``arsize,  // \
output npu_axi_region_t             AXIPREF``arregion,// \
// read data channel \
input  logic                        AXIPREF``rvalid,  // read data valid \
output logic                        AXIPREF``rready,  // read data accept \
input  logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
input  npu_axi_resp_t               AXIPREF``rresp,   // read response \
input  logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic                        AXIPREF``rlast,   // read last \
// write command channel \
output logic                        AXIPREF``awvalid, // write command valid \
input  logic                        AXIPREF``awready, // write command accept \
output logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_addr_t               AXIPREF``awaddr,  // \
output npu_axi_cache_t              AXIPREF``awcache, // \
output npu_axi_prot_t               AXIPREF``awprot,  // \
output npu_axi_lock_t               AXIPREF``awlock,  // \
output npu_axi_burst_t              AXIPREF``awburst, // \
output npu_axi_len_t                AXIPREF``awlen,   // \
output npu_axi_size_t               AXIPREF``awsize,  // \
output npu_axi_region_t             AXIPREF``awregion,// \
// write data channel \
output logic                        AXIPREF``wvalid,  // write data valid \
input  logic                        AXIPREF``wready,  // write data accept \
output logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
output logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
output logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic                        AXIPREF``wlast,   // write data last \
// write response channel \
input  logic                        AXIPREF``bvalid,  // write response valid \
output logic                        AXIPREF``bready,  // write response accept \
input  logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t               AXIPREF``bresp    // write response \

//
// AXI slave interface port on NPU module
//
`define AXISLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic                        AXIPREF``arvalid, // read command valid \
output logic                        AXIPREF``arready, // read command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_cmd_t                AXIPREF``ar,      // read command \
// read data channel \
output logic                        AXIPREF``rvalid,  // read data valid \
input  logic                        AXIPREF``rready,  // read data accept \
output logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
output npu_axi_resp_t               AXIPREF``rresp,   // read response \
output logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic                        AXIPREF``rlast,   // read last \
// write command channel \
input  logic                        AXIPREF``awvalid, // write command valid \
output logic                        AXIPREF``awready, // write command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
input  logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
input  npu_axi_cmd_t                AXIPREF``aw,      // write command \
// write data channel \
input  logic                        AXIPREF``wvalid,  // write data valid \
output logic                        AXIPREF``wready,  // write data accept \
input  logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
input  logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
input  logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
input  logic                        AXIPREF``wlast,   // write data last \
// write response channel \
output logic                        AXIPREF``bvalid,  // write response valid \
input  logic                        AXIPREF``bready,  // write response accept \
output logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
output logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
output npu_axi_resp_t               AXIPREF``bresp    // write response \

//
// AXI slave interface port on NPU module
//
`define AXINODATASLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic                        AXIPREF``arvalid, // read command valid \
output logic                        AXIPREF``arready, // read command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_cmd_t                AXIPREF``ar,      // read command \
// read data channel \
output logic                        AXIPREF``rvalid,  // read data valid \
input  logic                        AXIPREF``rready,  // read data accept \
output logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output npu_axi_resp_t               AXIPREF``rresp,   // read response \
output logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic                        AXIPREF``rlast,   // read last \
// write command channel \
input  logic                        AXIPREF``awvalid, // write command valid \
output logic                        AXIPREF``awready, // write command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
input  logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
input  npu_axi_cmd_t                AXIPREF``aw,      // write command \
// write data channel \
input  logic                        AXIPREF``wvalid,  // write data valid \
output logic                        AXIPREF``wready,  // write data accept \
input  logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
input  logic                        AXIPREF``wlast,   // write data last \
// write response channel \
output logic                        AXIPREF``bvalid,  // write response valid \
input  logic                        AXIPREF``bready,  // write response accept \
output logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
output logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
output npu_axi_resp_t               AXIPREF``bresp    // write response \

//
//
//
`define AXISLVN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic          [N-1:0]              AXIPREF``arvalid, // read command valid \
output logic          [N-1:0]              AXIPREF``arready, // read command accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_cmd_t  [N-1:0]              AXIPREF``ar,      // read command \
// read data channel \
output logic          [N-1:0]              AXIPREF``rvalid,  // read data valid \
input  logic          [N-1:0]              AXIPREF``rready,  // read data accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output logic          [N-1:0][AXIDW-1:0]   AXIPREF``rdata,   // read data \
output npu_axi_resp_t [N-1:0]              AXIPREF``rresp,   // read response \
output logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic          [N-1:0]              AXIPREF``rlast,   // read last \
// write command channel \
input  logic          [N-1:0]              AXIPREF``awvalid, // write command valid \
output logic          [N-1:0]              AXIPREF``awready, // write command accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
input  logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
input  npu_axi_cmd_t  [N-1:0]              AXIPREF``aw,      // write command \
// write data channel \
input  logic          [N-1:0]              AXIPREF``wvalid,  // write data valid \
output logic          [N-1:0]              AXIPREF``wready,  // write data accept \
input  logic          [N-1:0][AXIDW-1:0]   AXIPREF``wdata,   // write data \
input  logic          [N-1:0][AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
input  logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
input  logic          [N-1:0]              AXIPREF``wlast,   // write data last \
// write response channel \
output logic          [N-1:0]              AXIPREF``bvalid,  // write response valid \
input  logic          [N-1:0]              AXIPREF``bready,  // write response accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid,     // write response id \
output logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
output npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \
//
//
//
`define AXINODATASLVN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic          [N-1:0]              AXIPREF``arvalid, // read command valid \
output logic          [N-1:0]              AXIPREF``arready, // read command accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_cmd_t  [N-1:0]              AXIPREF``ar,      // read command \
// read data channel \
output logic          [N-1:0]              AXIPREF``rvalid,  // read data valid \
input  logic          [N-1:0]              AXIPREF``rready,  // read data accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output npu_axi_resp_t [N-1:0]              AXIPREF``rresp,   // read response \
output logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic          [N-1:0]              AXIPREF``rlast,   // read last \
// write command channel \
input  logic          [N-1:0]              AXIPREF``awvalid, // write command valid \
output logic          [N-1:0]              AXIPREF``awready, // write command accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
input  logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
input  npu_axi_cmd_t  [N-1:0]              AXIPREF``aw,      // write command \
// write data channel \
input  logic          [N-1:0]              AXIPREF``wvalid,  // write data valid \
output logic          [N-1:0]              AXIPREF``wready,  // write data accept \
input  logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
input  logic          [N-1:0]              AXIPREF``wlast,   // write data last \
// write response channel \
output logic          [N-1:0]              AXIPREF``bvalid,  // write response valid \
input  logic          [N-1:0]              AXIPREF``bready,  // write response accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid,     // write response id \
output logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
output npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \


//
//
//
`define AXISLV_EXT(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic                        AXIPREF``arvalid, // read command valid \
output logic                        AXIPREF``arready, // read command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_addr_t               AXIPREF``araddr,  // \
input  npu_axi_cache_t              AXIPREF``arcache, // \
input  npu_axi_prot_t               AXIPREF``arprot,  // \
input  npu_axi_lock_t               AXIPREF``arlock,  // \
input  npu_axi_burst_t              AXIPREF``arburst, // \
input  npu_axi_len_t                AXIPREF``arlen,   // \
input  npu_axi_size_t               AXIPREF``arsize,  // \
input  npu_axi_region_t             AXIPREF``arregion,// \
// read data channel \
output logic                        AXIPREF``rvalid,  // read data valid \
input  logic                        AXIPREF``rready,  // read data accept \
output logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
output npu_axi_resp_t               AXIPREF``rresp,   // read response \
output logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic                        AXIPREF``rlast,   // read last \
// write command channel \
input  logic                        AXIPREF``awvalid, // write command valid \
output logic                        AXIPREF``awready, // write command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
input  logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
input  npu_axi_addr_t               AXIPREF``awaddr,  // \
input  npu_axi_cache_t              AXIPREF``awcache, // \
input  npu_axi_prot_t               AXIPREF``awprot,  // \
input  npu_axi_lock_t               AXIPREF``awlock,  // \
input  npu_axi_burst_t              AXIPREF``awburst, // \
input  npu_axi_len_t                AXIPREF``awlen,   // \
input  npu_axi_size_t               AXIPREF``awsize,  // \
input  npu_axi_region_t             AXIPREF``awregion,// \
// write data channel \
input  logic                        AXIPREF``wvalid,  // write data valid \
output logic                        AXIPREF``wready,  // write data accept \
input  logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
input  logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
input  logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
input  logic                        AXIPREF``wlast,   // write data last \
// write response channel \
output logic                        AXIPREF``bvalid,  // write response valid \
input  logic                        AXIPREF``bready,  // write response accept \
output logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
output logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
output npu_axi_resp_t               AXIPREF``bresp    // write response \

// ----------------------------------------------------------------------------
// 
// ----------------------------------------------------------------------------


// i/oDMA use partial interface
//
// NPU AXI read instance port list
//
`define AXIRINST(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser  ), // read command user field \
.AXIPREF``ar      ( AXIWPREF``ar      ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid     ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata   ), // read data \
.AXIPREF``rresp   ( npu_axi_resp_t'(AXIWPREF``rresp)   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast   )  // read last \

//
// NPU AXI write instance port list
//
`define AXIWINST(AXIPREF,AXIWPREF) \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid    ), // write command ID \
.AXIPREF``awuser  ( AXIWPREF``awuser  ), // write command user field \
.AXIPREF``aw      ( AXIWPREF``aw      ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid  ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready  ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata   ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb   ), // write data strobe \
.AXIPREF``wuser   ( AXIWPREF``wuser   ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast   ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid  ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready  ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid     ), // write response id \
.AXIPREF``buser   ( AXIWPREF``buser   ), // read data user field \
.AXIPREF``bresp   ( npu_axi_resp_t'(AXIWPREF``bresp)   )  // write response \

//
// NPU AXI Read wire declaration
//
`define AXIRWIRES(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic                        AXIPREF``arvalid; // read command valid \
logic                        AXIPREF``arready; // read command accept \
logic          [AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_cmd_t                AXIPREF``ar;      // read command \
// read data channel \
logic                        AXIPREF``rvalid;  // read data valid \
logic                        AXIPREF``rready;  // read data accept \
logic          [AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [AXIDW-1:0]   AXIPREF``rdata;   // read data \
npu_axi_resp_t               AXIPREF``rresp;   // read response \
logic          [AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic                        AXIPREF``rlast    // read last \



//
// NPU AXI Write wire declaration
//
`define AXIWWIRES(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// write command channel \
logic                        AXIPREF``awvalid; // write command valid \
logic                        AXIPREF``awready; // write command accept \
logic          [AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_cmd_t                AXIPREF``aw;      // write command \
// write data channel \
logic                        AXIPREF``wvalid;  // write data valid \
logic                        AXIPREF``wready;  // write data accept \
logic          [AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic                        AXIPREF``wlast;   // write data last \
// write response channel \
logic                        AXIPREF``bvalid;  // write response valid \
logic                        AXIPREF``bready;  // write response accept \
logic          [AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t               AXIPREF``bresp    // write response \

//
// AXI master read interface port on NPU module
//
`define AXIRMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic                        AXIPREF``arvalid, // read command valid \
input  logic                        AXIPREF``arready, // read command accept \
output logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_cmd_t                AXIPREF``ar,      // read command \
// read data channel \
input  logic                        AXIPREF``rvalid,  // read data valid \
output logic                        AXIPREF``rready,  // read data accept \
input  logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
input  npu_axi_resp_t               AXIPREF``rresp,   // read response \
input  logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic                        AXIPREF``rlast    // read last \


//
// AXI master read interface port on NPU module
//
`define AXIWMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// write command channel \
output logic                        AXIPREF``awvalid, // write command valid \
input  logic                        AXIPREF``awready, // write command accept \
output logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_cmd_t                AXIPREF``aw,      // write command \
// write data channel \
output logic                        AXIPREF``wvalid,  // write data valid \
input  logic                        AXIPREF``wready,  // write data accept \
output logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
output logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
output logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic                        AXIPREF``wlast,   // write data last \
// write response channel \
input  logic                        AXIPREF``bvalid,  // write response valid \
output logic                        AXIPREF``bready,  // write response accept \
input  logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t               AXIPREF``bresp    // write response \

`define AXIRSLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic                        AXIPREF``arvalid, // read command valid \
output logic                        AXIPREF``arready, // read command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_cmd_t                AXIPREF``ar,      // read command \
// read data channel \
output logic                        AXIPREF``rvalid,  // read data valid \
input  logic                        AXIPREF``rready,  // read data accept \
output logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
output npu_axi_resp_t               AXIPREF``rresp,   // read response \
output logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic                        AXIPREF``rlast    // read last \


`define AXIRINST_M(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid    ), // read command ID \
.AXIPREF``aruser  ( AXIWPREF``aruser  ), // read command user field \
.AXIPREF``ar      ( AXIWPREF``ar      ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid  ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready  ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid     ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata   ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp   ), // read response \
.AXIPREF``ruser   ( AXIWPREF``ruser   ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast   )  // read last \


//
// Async AXI bridge split interface
//
// top-level async wires
`define AXIASYNCWIRES(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWL2,WL2,BL2,ARL2,RL2,AXIPREF) \
logic                                                                              AXIPREF``clk_req_a; \
logic [AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``aw_data; \
logic [`NUM_FLANES(AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t))-1:0][(1<<AWL2)-1:0]        AXIPREF``aw_rdpnt; \
logic [AWL2:0]                                                                     AXIPREF``aw_wpnt_a; \
logic [AWL2:0]                                                                     AXIPREF``aw_rpnt_a; \
logic [AXIDW+AXIDW/8+AXIWUW:0]                                                     AXIPREF``w_data; \
logic [`NUM_FLANES(AXIDW+AXIDW/8+AXIWUW+1)-1:0][(1<<WL2)-1:0]                      AXIPREF``w_rdpnt; \
logic [WL2:0]                                                                      AXIPREF``w_wpnt_a; \
logic [WL2:0]                                                                      AXIPREF``w_rpnt_a; \
logic [AXIIDW+AXIBUW+$bits(npu_axi_resp_t)-1:0]                                    AXIPREF``b_data; \
logic [`NUM_FLANES(AXIIDW+AXIBUW+$bits(npu_axi_resp_t))-1:0][(1<<BL2)-1:0]         AXIPREF``b_rdpnt; \
logic [BL2:0]                                                                      AXIPREF``b_wpnt_a; \
logic [BL2:0]                                                                      AXIPREF``b_rpnt_a; \
logic [AXIIDW+AXIARUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``ar_data; \
logic [`NUM_FLANES(AXIIDW+AXIARUW+$bits(npu_axi_cmd_t))-1:0][(1<<ARL2)-1:0]        AXIPREF``ar_rdpnt; \
logic [ARL2:0]                                                                     AXIPREF``ar_wpnt_a; \
logic [ARL2:0]                                                                     AXIPREF``ar_rpnt_a; \
logic [AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW:0]                                AXIPREF``r_data; \
logic [`NUM_FLANES(AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW+1)-1:0][(1<<RL2)-1:0] AXIPREF``r_rdpnt; \
logic [RL2:0]                                                                      AXIPREF``r_wpnt_a; \
logic [RL2:0]                                                                      AXIPREF``r_rpnt_a \

// top-level wire instance
`define AXIASYNCINST(AXIPREF,AXIWPREF) \
.AXIPREF``clk_req_a ( AXIWPREF``clk_req_a ), \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt_a ( AXIWPREF``aw_wpnt_a ), \
.AXIPREF``aw_rpnt_a ( AXIWPREF``aw_rpnt_a ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt_a  ( AXIWPREF``w_wpnt_a  ), \
.AXIPREF``w_rpnt_a  ( AXIWPREF``w_rpnt_a  ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt_a  ( AXIWPREF``b_wpnt_a  ), \
.AXIPREF``b_rpnt_a  ( AXIWPREF``b_rpnt_a  ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt_a ( AXIWPREF``ar_wpnt_a ), \
.AXIPREF``ar_rpnt_a ( AXIWPREF``ar_rpnt_a ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt_a  ( AXIWPREF``r_wpnt_a  ), \
.AXIPREF``r_rpnt_a  ( AXIWPREF``r_rpnt_a  ) \

`define AXIASYNCMINST(AXIPREF,AXIWPREF) \
.AXIPREF``clk_req   ( AXIWPREF``clk_req_a ), \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt   ( AXIWPREF``aw_wpnt_a ), \
.AXIPREF``aw_rpnt_a ( AXIWPREF``aw_rpnt_a ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt    ( AXIWPREF``w_wpnt_a  ), \
.AXIPREF``w_rpnt_a  ( AXIWPREF``w_rpnt_a  ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt_a  ( AXIWPREF``b_wpnt_a  ), \
.AXIPREF``b_rpnt    ( AXIWPREF``b_rpnt_a  ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt   ( AXIWPREF``ar_wpnt_a ), \
.AXIPREF``ar_rpnt_a ( AXIWPREF``ar_rpnt_a ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt_a  ( AXIWPREF``r_wpnt_a  ), \
.AXIPREF``r_rpnt    ( AXIWPREF``r_rpnt_a  ) \

`define AXIASYNCMSUB(AXIPREF,AXIWPREF) \
.AXIPREF``clk_req   ( AXIWPREF``clk_req   ), \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt   ( AXIWPREF``aw_wpnt   ), \
.AXIPREF``aw_rpnt_a ( AXIWPREF``aw_rpnt_a ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt    ( AXIWPREF``w_wpnt    ), \
.AXIPREF``w_rpnt_a  ( AXIWPREF``w_rpnt_a  ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt_a  ( AXIWPREF``b_wpnt_a  ), \
.AXIPREF``b_rpnt    ( AXIWPREF``b_rpnt    ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt   ( AXIWPREF``ar_wpnt   ), \
.AXIPREF``ar_rpnt_a ( AXIWPREF``ar_rpnt_a ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt_a  ( AXIWPREF``r_wpnt_a  ), \
.AXIPREF``r_rpnt    ( AXIWPREF``r_rpnt    ) \

`define AXIASYNCMSUBD(AXIPREF,AXIWPREF) \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt   ( AXIWPREF``aw_wpnt_a ), \
.AXIPREF``aw_rpnt_a ( AXIWPREF``aw_rpnt_a ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt    ( AXIWPREF``w_wpnt_a  ), \
.AXIPREF``w_rpnt_a  ( AXIWPREF``w_rpnt_a  ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt_a  ( AXIWPREF``b_wpnt_a  ), \
.AXIPREF``b_rpnt    ( AXIWPREF``b_rpnt_a  ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt   ( AXIWPREF``ar_wpnt_a ), \
.AXIPREF``ar_rpnt_a ( AXIWPREF``ar_rpnt_a ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt_a  ( AXIWPREF``r_wpnt_a  ), \
.AXIPREF``r_rpnt    ( AXIWPREF``r_rpnt_a  ) \


`define AXIASYNCSINST(AXIPREF,AXIWPREF) \
.AXIPREF``clk_req_a ( AXIWPREF``clk_req_a ), \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt_a ( AXIWPREF``aw_wpnt_a ), \
.AXIPREF``aw_rpnt   ( AXIWPREF``aw_rpnt_a ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt_a  ( AXIWPREF``w_wpnt_a  ), \
.AXIPREF``w_rpnt    ( AXIWPREF``w_rpnt_a  ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt    ( AXIWPREF``b_wpnt_a  ), \
.AXIPREF``b_rpnt_a  ( AXIWPREF``b_rpnt_a  ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt_a ( AXIWPREF``ar_wpnt_a ), \
.AXIPREF``ar_rpnt   ( AXIWPREF``ar_rpnt_a ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt    ( AXIWPREF``r_wpnt_a  ), \
.AXIPREF``r_rpnt_a  ( AXIWPREF``r_rpnt_a  ) \

`define AXIASYNCSSUBD(AXIPREF,AXIWPREF) \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt_a ( AXIWPREF``aw_wpnt_a ), \
.AXIPREF``aw_rpnt   ( AXIWPREF``aw_rpnt_a ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt_a  ( AXIWPREF``w_wpnt_a  ), \
.AXIPREF``w_rpnt    ( AXIWPREF``w_rpnt_a  ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt    ( AXIWPREF``b_wpnt_a  ), \
.AXIPREF``b_rpnt_a  ( AXIWPREF``b_rpnt_a  ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt_a ( AXIWPREF``ar_wpnt_a ), \
.AXIPREF``ar_rpnt   ( AXIWPREF``ar_rpnt_a ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt    ( AXIWPREF``r_wpnt_a  ), \
.AXIPREF``r_rpnt_a  ( AXIWPREF``r_rpnt_a  ) \

`define AXIASYNCSSUB(AXIPREF,AXIWPREF) \
.AXIPREF``clk_req_a ( AXIWPREF``clk_req_a ), \
.AXIPREF``aw_data   ( AXIWPREF``aw_data   ), \
.AXIPREF``aw_rdpnt  ( AXIWPREF``aw_rdpnt  ), \
.AXIPREF``aw_wpnt_a ( AXIWPREF``aw_wpnt_a ), \
.AXIPREF``aw_rpnt   ( AXIWPREF``aw_rpnt   ), \
.AXIPREF``w_data    ( AXIWPREF``w_data    ), \
.AXIPREF``w_rdpnt   ( AXIWPREF``w_rdpnt   ), \
.AXIPREF``w_wpnt_a  ( AXIWPREF``w_wpnt_a  ), \
.AXIPREF``w_rpnt    ( AXIWPREF``w_rpnt    ), \
.AXIPREF``b_data    ( AXIWPREF``b_data    ), \
.AXIPREF``b_rdpnt   ( AXIWPREF``b_rdpnt   ), \
.AXIPREF``b_wpnt    ( AXIWPREF``b_wpnt    ), \
.AXIPREF``b_rpnt_a  ( AXIWPREF``b_rpnt_a  ), \
.AXIPREF``ar_data   ( AXIWPREF``ar_data   ), \
.AXIPREF``ar_rdpnt  ( AXIWPREF``ar_rdpnt  ), \
.AXIPREF``ar_wpnt_a ( AXIWPREF``ar_wpnt_a ), \
.AXIPREF``ar_rpnt   ( AXIWPREF``ar_rpnt   ), \
.AXIPREF``r_data    ( AXIWPREF``r_data    ), \
.AXIPREF``r_rdpnt   ( AXIWPREF``r_rdpnt   ), \
.AXIPREF``r_wpnt    ( AXIWPREF``r_wpnt    ), \
.AXIPREF``r_rpnt_a  ( AXIWPREF``r_rpnt_a  ) \

`define AXIASYNCMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWL2,WL2,BL2,ARL2,RL2,AXIPREF) \
output logic                                                                              AXIPREF``clk_req, \
output logic [AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``aw_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t))-1:0][(1<<AWL2)-1:0]        AXIPREF``aw_rdpnt, \
output logic [AWL2:0]                                                                     AXIPREF``aw_wpnt, \
input  logic [AWL2:0]                                                                     AXIPREF``aw_rpnt_a, \
output logic [AXIDW+AXIDW/8+AXIWUW:0]                                                     AXIPREF``w_data, \
input  logic [`NUM_FLANES(AXIDW+AXIDW/8+AXIWUW+1)-1:0][(1<<WL2)-1:0]                      AXIPREF``w_rdpnt, \
output logic [WL2:0]                                                                      AXIPREF``w_wpnt, \
input  logic [WL2:0]                                                                      AXIPREF``w_rpnt_a, \
input  logic [AXIIDW+AXIBUW+$bits(npu_axi_resp_t)-1:0]                                    AXIPREF``b_data, \
output logic [`NUM_FLANES(AXIIDW+AXIBUW+$bits(npu_axi_resp_t))-1:0][(1<<BL2)-1:0]         AXIPREF``b_rdpnt, \
input  logic [BL2:0]                                                                      AXIPREF``b_wpnt_a, \
output logic [BL2:0]                                                                      AXIPREF``b_rpnt, \
output logic [AXIIDW+AXIARUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``ar_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIARUW+$bits(npu_axi_cmd_t))-1:0][(1<<ARL2)-1:0]        AXIPREF``ar_rdpnt, \
output logic [ARL2:0]                                                                     AXIPREF``ar_wpnt, \
input  logic [ARL2:0]                                                                     AXIPREF``ar_rpnt_a, \
input  logic [AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW:0]                                AXIPREF``r_data, \
output logic [`NUM_FLANES(AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW+1)-1:0][(1<<RL2)-1:0] AXIPREF``r_rdpnt, \
input  logic [RL2:0]                                                                      AXIPREF``r_wpnt_a, \
output logic [RL2:0]                                                                      AXIPREF``r_rpnt \

`define AXIASYNCSLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWL2,WL2,BL2,ARL2,RL2,AXIPREF) \
input  logic                                                                              AXIPREF``clk_req_a, \
input  logic [AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``aw_data, \
output logic [`NUM_FLANES(AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t))-1:0][(1<<AWL2)-1:0]        AXIPREF``aw_rdpnt, \
input  logic [AWL2:0]                                                                     AXIPREF``aw_wpnt_a, \
output logic [AWL2:0]                                                                     AXIPREF``aw_rpnt, \
input  logic [AXIDW+AXIDW/8+AXIWUW:0]                                                     AXIPREF``w_data, \
output logic [`NUM_FLANES(AXIDW+AXIDW/8+AXIWUW+1)-1:0][(1<<WL2)-1:0]                      AXIPREF``w_rdpnt, \
input  logic [WL2:0]                                                                      AXIPREF``w_wpnt_a, \
output logic [WL2:0]                                                                      AXIPREF``w_rpnt, \
output logic [AXIIDW+AXIBUW+$bits(npu_axi_resp_t)-1:0]                                    AXIPREF``b_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIBUW+$bits(npu_axi_resp_t))-1:0][(1<<BL2)-1:0]         AXIPREF``b_rdpnt, \
output logic [BL2:0]                                                                      AXIPREF``b_wpnt, \
input  logic [BL2:0]                                                                      AXIPREF``b_rpnt_a, \
input  logic [AXIIDW+AXIARUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``ar_data, \
output logic [`NUM_FLANES(AXIIDW+AXIARUW+$bits(npu_axi_cmd_t))-1:0][(1<<ARL2)-1:0]        AXIPREF``ar_rdpnt, \
input  logic [ARL2:0]                                                                     AXIPREF``ar_wpnt_a, \
output logic [ARL2:0]                                                                     AXIPREF``ar_rpnt, \
output logic [AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW:0]                                AXIPREF``r_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW+1)-1:0][(1<<RL2)-1:0] AXIPREF``r_rdpnt, \
output logic [RL2:0]                                                                      AXIPREF``r_wpnt, \
input  logic [RL2:0]                                                                      AXIPREF``r_rpnt_a \


//
// Sync AXI bridge split interface
//
// top-level sync wires
`define AXISYNCWIRES(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWL2,WL2,BL2,ARL2,RL2,AXIPREF) \
logic                                                                              AXIPREF``clk_req; \
logic [AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``aw_data; \
logic [`NUM_FLANES(AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t))-1:0][(1<<AWL2)-1:0]        AXIPREF``aw_rdpnt; \
logic [AWL2:0]                                                                     AXIPREF``aw_wpnt; \
logic [AWL2:0]                                                                     AXIPREF``aw_rpnt; \
logic [AXIDW+AXIDW/8+AXIWUW:0]                                                     AXIPREF``w_data; \
logic [`NUM_FLANES(AXIDW+AXIDW/8+AXIWUW+1)-1:0][(1<<WL2)-1:0]                      AXIPREF``w_rdpnt; \
logic [WL2:0]                                                                      AXIPREF``w_wpnt; \
logic [WL2:0]                                                                      AXIPREF``w_rpnt; \
logic [AXIIDW+AXIBUW+$bits(npu_axi_resp_t)-1:0]                                    AXIPREF``b_data; \
logic [`NUM_FLANES(AXIIDW+AXIBUW+$bits(npu_axi_resp_t))-1:0][(1<<BL2)-1:0]         AXIPREF``b_rdpnt; \
logic [BL2:0]                                                                      AXIPREF``b_wpnt; \
logic [BL2:0]                                                                      AXIPREF``b_rpnt; \
logic [AXIIDW+AXIARUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``ar_data; \
logic [`NUM_FLANES(AXIIDW+AXIARUW+$bits(npu_axi_cmd_t))-1:0][(1<<ARL2)-1:0]        AXIPREF``ar_rdpnt; \
logic [ARL2:0]                                                                     AXIPREF``ar_wpnt; \
logic [ARL2:0]                                                                     AXIPREF``ar_rpnt; \
logic [AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW:0]                                AXIPREF``r_data; \
logic [`NUM_FLANES(AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW+1)-1:0][(1<<RL2)-1:0] AXIPREF``r_rdpnt; \
logic [RL2:0]                                                                      AXIPREF``r_wpnt; \
logic [RL2:0]                                                                      AXIPREF``r_rpnt \

`define AXISYNCASG(AXIPREF,AXIWPREF) \
assign  AXIWPREF``aw_rdpnt  =   AXIPREF``aw_rdpnt; \
assign  AXIWPREF``aw_rpnt   =   AXIPREF``aw_rpnt ; \
assign  AXIWPREF``w_rdpnt   =   AXIPREF``w_rdpnt ; \
assign  AXIWPREF``w_rpnt    =   AXIPREF``w_rpnt  ; \
assign  AXIWPREF``b_data    =   AXIPREF``b_data  ; \
assign  AXIWPREF``b_wpnt    =   AXIPREF``b_wpnt  ; \
assign  AXIWPREF``ar_rdpnt  =   AXIPREF``ar_rdpnt; \
assign  AXIWPREF``ar_rpnt   =   AXIPREF``ar_rpnt ; \
assign  AXIWPREF``r_data    =   AXIPREF``r_data  ; \
assign  AXIWPREF``r_wpnt    =   AXIPREF``r_wpnt  ; \
assign  AXIPREF``clk_req    =   AXIWPREF``clk_req ; \
assign  AXIPREF``aw_data    =   AXIWPREF``aw_data ; \
assign  AXIPREF``aw_wpnt    =   AXIWPREF``aw_wpnt ; \
assign  AXIPREF``w_data     =   AXIWPREF``w_data  ; \
assign  AXIPREF``w_wpnt     =   AXIWPREF``w_wpnt  ; \
assign  AXIPREF``b_rdpnt    =   AXIWPREF``b_rdpnt ; \
assign  AXIPREF``b_rpnt     =   AXIWPREF``b_rpnt  ; \
assign  AXIPREF``ar_data    =   AXIWPREF``ar_data ; \
assign  AXIPREF``ar_wpnt    =   AXIWPREF``ar_wpnt ; \
assign  AXIPREF``r_rdpnt    =   AXIWPREF``r_rdpnt ; \
assign  AXIPREF``r_rpnt     =   AXIWPREF``r_rpnt    \


// top-level wire instance
`define AXISYNCINST(AXIPREF,AXIWPREF) \
.AXIPREF``clk_req  ( AXIWPREF``clk_req  ), \
.AXIPREF``aw_data  ( AXIWPREF``aw_data  ), \
.AXIPREF``aw_rdpnt ( AXIWPREF``aw_rdpnt ), \
.AXIPREF``aw_wpnt  ( AXIWPREF``aw_wpnt  ), \
.AXIPREF``aw_rpnt  ( AXIWPREF``aw_rpnt  ), \
.AXIPREF``w_data   ( AXIWPREF``w_data   ), \
.AXIPREF``w_rdpnt  ( AXIWPREF``w_rdpnt  ), \
.AXIPREF``w_wpnt   ( AXIWPREF``w_wpnt   ), \
.AXIPREF``w_rpnt   ( AXIWPREF``w_rpnt   ), \
.AXIPREF``b_data   ( AXIWPREF``b_data   ), \
.AXIPREF``b_rdpnt  ( AXIWPREF``b_rdpnt  ), \
.AXIPREF``b_wpnt   ( AXIWPREF``b_wpnt   ), \
.AXIPREF``b_rpnt   ( AXIWPREF``b_rpnt   ), \
.AXIPREF``ar_data  ( AXIWPREF``ar_data  ), \
.AXIPREF``ar_rdpnt ( AXIWPREF``ar_rdpnt ), \
.AXIPREF``ar_wpnt  ( AXIWPREF``ar_wpnt  ), \
.AXIPREF``ar_rpnt  ( AXIWPREF``ar_rpnt  ), \
.AXIPREF``r_data   ( AXIWPREF``r_data   ), \
.AXIPREF``r_rdpnt  ( AXIWPREF``r_rdpnt  ), \
.AXIPREF``r_wpnt   ( AXIWPREF``r_wpnt   ), \
.AXIPREF``r_rpnt   ( AXIWPREF``r_rpnt   ) \

`define AXISYNCMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWL2,WL2,BL2,ARL2,RL2,AXIPREF) \
output logic                                                                              AXIPREF``clk_req, \
output logic [AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``aw_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t))-1:0][(1<<AWL2)-1:0]        AXIPREF``aw_rdpnt, \
output logic [AWL2:0]                                                                     AXIPREF``aw_wpnt, \
input  logic [AWL2:0]                                                                     AXIPREF``aw_rpnt, \
output logic [AXIDW+AXIDW/8+AXIWUW:0]                                                     AXIPREF``w_data, \
input  logic [`NUM_FLANES(AXIDW+AXIDW/8+AXIWUW+1)-1:0][(1<<WL2)-1:0]                      AXIPREF``w_rdpnt, \
output logic [WL2:0]                                                                      AXIPREF``w_wpnt, \
input  logic [WL2:0]                                                                      AXIPREF``w_rpnt, \
input  logic [AXIIDW+AXIBUW+$bits(npu_axi_resp_t)-1:0]                                    AXIPREF``b_data, \
output logic [`NUM_FLANES(AXIIDW+AXIBUW+$bits(npu_axi_resp_t))-1:0][(1<<BL2)-1:0]         AXIPREF``b_rdpnt, \
input  logic [BL2:0]                                                                      AXIPREF``b_wpnt, \
output logic [BL2:0]                                                                      AXIPREF``b_rpnt, \
output logic [AXIIDW+AXIARUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``ar_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIARUW+$bits(npu_axi_cmd_t))-1:0][(1<<ARL2)-1:0]        AXIPREF``ar_rdpnt, \
output logic [ARL2:0]                                                                     AXIPREF``ar_wpnt, \
input  logic [ARL2:0]                                                                     AXIPREF``ar_rpnt, \
input  logic [AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW:0]                                AXIPREF``r_data, \
output logic [`NUM_FLANES(AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW+1)-1:0][(1<<RL2)-1:0] AXIPREF``r_rdpnt, \
input  logic [RL2:0]                                                                      AXIPREF``r_wpnt, \
output logic [RL2:0]                                                                      AXIPREF``r_rpnt \

`define AXISYNCSLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWL2,WL2,BL2,ARL2,RL2,AXIPREF) \
input  logic                                                                              AXIPREF``clk_req, \
input  logic [AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``aw_data, \
output logic [`NUM_FLANES(AXIIDW+AXIAWUW+$bits(npu_axi_cmd_t))-1:0][(1<<AWL2)-1:0]        AXIPREF``aw_rdpnt, \
input  logic [AWL2:0]                                                                     AXIPREF``aw_wpnt, \
output logic [AWL2:0]                                                                     AXIPREF``aw_rpnt, \
input  logic [AXIDW+AXIDW/8+AXIWUW:0]                                                     AXIPREF``w_data, \
output logic [`NUM_FLANES(AXIDW+AXIDW/8+AXIWUW+1)-1:0][(1<<WL2)-1:0]                      AXIPREF``w_rdpnt, \
input  logic [WL2:0]                                                                      AXIPREF``w_wpnt, \
output logic [WL2:0]                                                                      AXIPREF``w_rpnt, \
output logic [AXIIDW+AXIBUW+$bits(npu_axi_resp_t)-1:0]                                    AXIPREF``b_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIBUW+$bits(npu_axi_resp_t))-1:0][(1<<BL2)-1:0]         AXIPREF``b_rdpnt, \
output logic [BL2:0]                                                                      AXIPREF``b_wpnt, \
input  logic [BL2:0]                                                                      AXIPREF``b_rpnt, \
input  logic [AXIIDW+AXIARUW+$bits(npu_axi_cmd_t)-1:0]                                    AXIPREF``ar_data, \
output logic [`NUM_FLANES(AXIIDW+AXIARUW+$bits(npu_axi_cmd_t))-1:0][(1<<ARL2)-1:0]        AXIPREF``ar_rdpnt, \
input  logic [ARL2:0]                                                                     AXIPREF``ar_wpnt, \
output logic [ARL2:0]                                                                     AXIPREF``ar_rpnt, \
output logic [AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW:0]                                AXIPREF``r_data, \
input  logic [`NUM_FLANES(AXIIDW+AXIDW+$bits(npu_axi_resp_t)+AXIRUW+1)-1:0][(1<<RL2)-1:0] AXIPREF``r_rdpnt, \
output logic [RL2:0]                                                                      AXIPREF``r_wpnt, \
input  logic [RL2:0]                                                                      AXIPREF``r_rpnt \


//
// AXI with wide len
//
`define AXILWIRES(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic                        AXIPREF``arvalid; // read command valid \
logic                        AXIPREF``arready; // read command accept \
logic          [AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_wcmd_t               AXIPREF``ar;      // read command \
// read data channel \
logic                        AXIPREF``rvalid;  // read data valid \
logic                        AXIPREF``rready;  // read data accept \
logic          [AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [AXIDW-1:0]   AXIPREF``rdata;   // read data \
npu_axi_resp_t               AXIPREF``rresp;   // read response \
logic          [AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic                        AXIPREF``rlast;   // read last \
// write command channel \
logic                        AXIPREF``awvalid; // write command valid \
logic                        AXIPREF``awready; // write command accept \
logic          [AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_wcmd_t               AXIPREF``aw;      // write command \
// write data channel \
logic                        AXIPREF``wvalid;  // write data valid \
logic                        AXIPREF``wready;  // write data accept \
logic          [AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic                        AXIPREF``wlast;   // write data last \
// write response channel \
logic                        AXIPREF``bvalid;  // write response valid \
logic                        AXIPREF``bready;  // write response accept \
logic          [AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t               AXIPREF``bresp    // write response \

`define AXILWIRESN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
logic          [N-1:0]              AXIPREF``arvalid; // read command valid \
logic          [N-1:0]              AXIPREF``arready; // read command accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid;    // read command ID \
logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser;  // read command user field \
npu_axi_wcmd_t [N-1:0]              AXIPREF``ar;      // read command \
// read data channel \
logic          [N-1:0]              AXIPREF``rvalid;  // read data valid \
logic          [N-1:0]              AXIPREF``rready;  // read data accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid;     // read data id \
logic          [N-1:0][AXIDW-1:0]   AXIPREF``rdata;   // read data \
npu_axi_resp_t [N-1:0]              AXIPREF``rresp;   // read response \
logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser;   // read data user field \
logic          [N-1:0]              AXIPREF``rlast;   // read last \
// write command channel \
logic          [N-1:0]              AXIPREF``awvalid; // write command valid \
logic          [N-1:0]              AXIPREF``awready; // write command accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid;    // write command ID \
logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser;  // write command user field \
npu_axi_wcmd_t [N-1:0]              AXIPREF``aw;      // write command \
// write data channel \
logic          [N-1:0]              AXIPREF``wvalid;  // write data valid \
logic          [N-1:0]              AXIPREF``wready;  // write data accept \
logic          [N-1:0][AXIDW-1:0]   AXIPREF``wdata;   // write data \
logic          [N-1:0][AXIDW/8-1:0] AXIPREF``wstrb;   // write data strobe \
logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser;   // write data user field \
logic          [N-1:0]              AXIPREF``wlast;   // write data last \
// write response channel \
logic          [N-1:0]              AXIPREF``bvalid;  // write response valid \
logic          [N-1:0]              AXIPREF``bready;  // write response accept \
logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid;     // write response id \
logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser;   // read data user field \
npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \

`define AXILSLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
input  logic                        AXIPREF``arvalid, // read command valid \
output logic                        AXIPREF``arready, // read command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
input  logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
input  npu_axi_wcmd_t               AXIPREF``ar,      // read command \
// read data channel \
output logic                        AXIPREF``rvalid,  // read data valid \
input  logic                        AXIPREF``rready,  // read data accept \
output logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
output logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
output npu_axi_resp_t               AXIPREF``rresp,   // read response \
output logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
output logic                        AXIPREF``rlast,   // read last \
// write command channel \
input  logic                        AXIPREF``awvalid, // write command valid \
output logic                        AXIPREF``awready, // write command accept \
input  logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
input  logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
input  npu_axi_wcmd_t               AXIPREF``aw,      // write command \
// write data channel \
input  logic                        AXIPREF``wvalid,  // write data valid \
output logic                        AXIPREF``wready,  // write data accept \
input  logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
input  logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
input  logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
input  logic                        AXIPREF``wlast,   // write data last \
// write response channel \
output logic                        AXIPREF``bvalid,  // write response valid \
input  logic                        AXIPREF``bready,  // write response accept \
output logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
output logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
output npu_axi_resp_t               AXIPREF``bresp    // write response \

`define AXILMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic                        AXIPREF``arvalid, // read command valid \
input  logic                        AXIPREF``arready, // read command accept \
output logic          [AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_wcmd_t               AXIPREF``ar,      // read command \
// read data channel \
input  logic                        AXIPREF``rvalid,  // read data valid \
output logic                        AXIPREF``rready,  // read data accept \
input  logic          [AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  logic          [AXIDW-1:0]   AXIPREF``rdata,   // read data \
input  npu_axi_resp_t               AXIPREF``rresp,   // read response \
input  logic          [AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic                        AXIPREF``rlast,   // read last \
// write command channel \
output logic                        AXIPREF``awvalid, // write command valid \
input  logic                        AXIPREF``awready, // write command accept \
output logic          [AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_wcmd_t               AXIPREF``aw,      // write command \
// write data channel \
output logic                        AXIPREF``wvalid,  // write data valid \
input  logic                        AXIPREF``wready,  // write data accept \
output logic          [AXIDW-1:0]   AXIPREF``wdata,   // write data \
output logic          [AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
output logic          [AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic                        AXIPREF``wlast,   // write data last \
// write response channel \
input  logic                        AXIPREF``bvalid,  // write response valid \
output logic                        AXIPREF``bready,  // write response accept \
input  logic          [AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t               AXIPREF``bresp    // write response \

`define AXILMSTN(N,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
// read command channel \
output logic          [N-1:0]              AXIPREF``arvalid, // read command valid \
input  logic          [N-1:0]              AXIPREF``arready, // read command accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``arid,    // read command ID \
output logic          [N-1:0][AXIARUW-1:0] AXIPREF``aruser,  // read command user field \
output npu_axi_wcmd_t [N-1:0]              AXIPREF``ar,      // read command \
// read data channel \
input  logic          [N-1:0]              AXIPREF``rvalid,  // read data valid \
output logic          [N-1:0]              AXIPREF``rready,  // read data accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``rid,     // read data id \
input  logic          [N-1:0][AXIDW-1:0]   AXIPREF``rdata,   // read data \
input  npu_axi_resp_t [N-1:0]              AXIPREF``rresp,   // read response \
input  logic          [N-1:0][AXIRUW-1:0]  AXIPREF``ruser,   // read data user field \
input  logic          [N-1:0]              AXIPREF``rlast,   // read last \
// write command channel \
output logic          [N-1:0]              AXIPREF``awvalid, // write command valid \
input  logic          [N-1:0]              AXIPREF``awready, // write command accept \
output logic          [N-1:0][AXIIDW-1:0]  AXIPREF``awid,    // write command ID \
output logic          [N-1:0][AXIAWUW-1:0] AXIPREF``awuser,  // write command user field \
output npu_axi_wcmd_t [N-1:0]              AXIPREF``aw,      // write command \
// write data channel \
output logic          [N-1:0]              AXIPREF``wvalid,  // write data valid \
input  logic          [N-1:0]              AXIPREF``wready,  // write data accept \
output logic          [N-1:0][AXIDW-1:0]   AXIPREF``wdata,   // write data \
output logic          [N-1:0][AXIDW/8-1:0] AXIPREF``wstrb,   // write data strobe \
output logic          [N-1:0][AXIWUW-1:0]  AXIPREF``wuser,   // write data user field \
output logic          [N-1:0]              AXIPREF``wlast,   // write data last \
// write response channel \
input  logic          [N-1:0]              AXIPREF``bvalid,  // write response valid \
output logic          [N-1:0]              AXIPREF``bready,  // write response accept \
input  logic          [N-1:0][AXIIDW-1:0]  AXIPREF``bid,     // write response id \
input  logic          [N-1:0][AXIBUW-1:0]  AXIPREF``buser,   // read data user field \
input  npu_axi_resp_t [N-1:0]              AXIPREF``bresp    // write response \

//
// AXI configuration interface
//
`define AXICONFIGWIRES(NUMAP,NUMMST,PFX) \
logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] PFX``decbase; \
logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] PFX``decsize; \
logic [NUMAP-1:0][NUMMST-1:0]          PFX``decmst

`define AXICONFIGINST(PFX) \
.decbase ( PFX``decbase ), \
.decsize ( PFX``decsize ), \
.decmst  ( PFX``decmst  )

`define AXICONFIGASGN(NUMAP,IDX,PFXA,PFXB) \
assign PFXA``decbase = PFXB``decbase[IDX+:NUMAP]; \
assign PFXA``decsize = PFXB``decsize[IDX+:NUMAP]; \
assign PFXA``decmst  = PFXB``decmst[IDX+:NUMAP]

`define AXICONFIGASGM(NUMAP,IDX,PFXA,PFXB) \
assign PFXB``decbase[IDX+:NUMAP] = PFXA``decbase; \
assign PFXB``decsize[IDX+:NUMAP] = PFXA``decsize; \
assign PFXB``decmst[IDX+:NUMAP]  = PFXA``decmst 

//
// CLN AXI Connections
//
`define CLN_AXISLV_INST(AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid      ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready      ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid         ), // read command ID \
//.AXIPREF``aruser  ( AXIWPREF``aruser       ), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``araddr      ), // read command \
.AXIPREF``arsize  ( AXIWPREF``arsize      ), // read command \
.AXIPREF``arlen   ( AXIWPREF``arlen        ), // read command \
.AXIPREF``arburst ( AXIWPREF``arburst[1:0]), // read command \
.AXIPREF``arlock  ( AXIWPREF``arlock[0]   ), // read command \
.AXIPREF``arprot  ( AXIWPREF``arprot      ), // read command \
.AXIPREF``arcache ( AXIWPREF``arcache     ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid       ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready       ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid          ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata        ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp[1:0]   ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser        ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast        ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid      ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready      ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid         ), // write command ID \
//.AXIPREF``awuser  ( AXIWPREF``awuser       ), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``awaddr      ), // write command \
.AXIPREF``awsize  ( AXIWPREF``awsize      ), // write command \
.AXIPREF``awlen   ( AXIWPREF``awlen        ), // write command \
.AXIPREF``awburst ( AXIWPREF``awburst[1:0]), // write command \
.AXIPREF``awlock  ( AXIWPREF``awlock[0]   ), // write command \
.AXIPREF``awprot  ( AXIWPREF``awprot      ), // write command \
.AXIPREF``awcache ( AXIWPREF``awcache     ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid       ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready       ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata        ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb        ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser        ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast        ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid       ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready       ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid          ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser        ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[1:0]   )  // write response \

//
//
//
`define CLN_AXIMST_NOUSR_INSTN(AW,AXIPREF,AXIWPREF,N) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid[N]      ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready[N]      ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid[N]         ), // read command ID \
//.AXIPREF``aruser  ( {2'b0,AXIWPREF``aruser[N]}), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``ar[N].addr[AW-1:0]), // read command \
.AXIPREF``arsize  ( AXIWPREF``ar[N].size      ), // read command \
.AXIPREF``arlen   ( {4'b0,AXIWPREF``ar[N].len}), // read command \
.AXIPREF``arburst ( AXIWPREF``ar[N].burst[1:0]), // read command \
.AXIPREF``arlock  ( AXIWPREF``ar[N].lock[0]   ), // read command \
.AXIPREF``arprot  ( AXIWPREF``ar[N].prot      ), // read command \
.AXIPREF``arcache ( AXIWPREF``ar[N].cache     ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid[N]       ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready[N]       ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid[N]          ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata[N]        ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp[N][1:0]   ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser[N]        ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast[N]        ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid[N]      ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready[N]      ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid[N]         ), // write command ID \
//.AXIPREF``awuser  ( {2'b0,AXIWPREF``awuser[N]}), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``aw[N].addr[AW-1:0]), // write command \
.AXIPREF``awsize  ( AXIWPREF``aw[N].size      ), // write command \
.AXIPREF``awlen   ( {4'b0,AXIWPREF``aw[N].len}), // write command \
.AXIPREF``awburst ( AXIWPREF``aw[N].burst[1:0]), // write command \
.AXIPREF``awlock  ( AXIWPREF``aw[N].lock[0]   ), // write command \
.AXIPREF``awprot  ( AXIWPREF``aw[N].prot      ), // write command \
.AXIPREF``awcache ( AXIWPREF``aw[N].cache     ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid[N]       ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready[N]       ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata[N]        ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb[N]        ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser[N]        ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast[N]        ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid[N]       ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready[N]       ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid[N]          ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser[N]        ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[N][1:0]   )  // write response \

//
//
//
`define CLN_AXIMST_INSTN(AW,AXIPREF,AXIWPREF,N) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid[N]      ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready[N]      ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid[N]         ), // read command ID \
.AXIPREF``aruser  ( {2'b0,AXIWPREF``aruser[N]}), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``ar[N].addr[AW-1:0]), // read command \
.AXIPREF``arsize  ( AXIWPREF``ar[N].size      ), // read command \
.AXIPREF``arlen   ( {4'b0,AXIWPREF``ar[N].len}), // read command \
.AXIPREF``arburst ( AXIWPREF``ar[N].burst[1:0]), // read command \
.AXIPREF``arlock  ( AXIWPREF``ar[N].lock[0]   ), // read command \
.AXIPREF``arprot  ( AXIWPREF``ar[N].prot      ), // read command \
.AXIPREF``arcache ( AXIWPREF``ar[N].cache     ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid[N]       ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready[N]       ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid[N]          ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata[N]        ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp[N][1:0]   ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser[N]        ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast[N]        ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid[N]      ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready[N]      ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid[N]         ), // write command ID \
.AXIPREF``awuser  ( {2'b0,AXIWPREF``awuser[N]}), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``aw[N].addr[AW-1:0]), // write command \
.AXIPREF``awsize  ( AXIWPREF``aw[N].size      ), // write command \
.AXIPREF``awlen   ( {4'b0,AXIWPREF``aw[N].len}), // write command \
.AXIPREF``awburst ( AXIWPREF``aw[N].burst[1:0]), // write command \
.AXIPREF``awlock  ( AXIWPREF``aw[N].lock[0]   ), // write command \
.AXIPREF``awprot  ( AXIWPREF``aw[N].prot      ), // write command \
.AXIPREF``awcache ( AXIWPREF``aw[N].cache     ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid[N]       ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready[N]       ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata[N]        ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb[N]        ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser[N]        ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast[N]        ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid[N]       ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready[N]       ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid[N]          ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser[N]        ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[N][1:0]   )  // write response \

`define CLN_AXIMST_INST(AW,AXIPREF,AXIWPREF) \
// read command channel \
.AXIPREF``arvalid ( AXIWPREF``arvalid      ), // read command valid \
.AXIPREF``arready ( AXIWPREF``arready      ), // read command accept \
.AXIPREF``arid    ( AXIWPREF``arid         ), // read command ID \
.AXIPREF``aruser  ( {2'b0,AXIWPREF``aruser}), // read command user field \
.AXIPREF``araddr  ( AXIWPREF``ar.addr[AW-1:0]), // read command \
.AXIPREF``arsize  ( AXIWPREF``ar.size      ), // read command \
.AXIPREF``arlen   ( {4'b0,AXIWPREF``ar.len}), // read command \
.AXIPREF``arburst ( AXIWPREF``ar.burst[1:0]), // read command \
.AXIPREF``arlock  ( AXIWPREF``ar.lock[0]   ), // read command \
.AXIPREF``arprot  ( AXIWPREF``ar.prot      ), // read command \
.AXIPREF``arcache ( AXIWPREF``ar.cache     ), // read command \
// read data channel \
.AXIPREF``rvalid  ( AXIWPREF``rvalid       ), // read data valid \
.AXIPREF``rready  ( AXIWPREF``rready       ), // read data accept \
.AXIPREF``rid     ( AXIWPREF``rid          ), // read data id \
.AXIPREF``rdata   ( AXIWPREF``rdata        ), // read data \
.AXIPREF``rresp   ( AXIWPREF``rresp[1:0]   ), // read response \
//.AXIPREF``ruser   ( AXIWPREF``ruser        ), // read data user field \
.AXIPREF``rlast   ( AXIWPREF``rlast        ), // read last \
// write command channel \
.AXIPREF``awvalid ( AXIWPREF``awvalid      ), // write command valid \
.AXIPREF``awready ( AXIWPREF``awready      ), // write command accept \
.AXIPREF``awid    ( AXIWPREF``awid         ), // write command ID \
.AXIPREF``awuser  ( {2'b0,AXIWPREF``awuser}), // write command user field \
.AXIPREF``awaddr  ( AXIWPREF``aw.addr[AW-1:0]), // write command \
.AXIPREF``awsize  ( AXIWPREF``aw.size      ), // write command \
.AXIPREF``awlen   ( {4'b0,AXIWPREF``aw.len}), // write command \
.AXIPREF``awburst ( AXIWPREF``aw.burst[1:0]), // write command \
.AXIPREF``awlock  ( AXIWPREF``aw.lock[0]   ), // write command \
.AXIPREF``awprot  ( AXIWPREF``aw.prot      ), // write command \
.AXIPREF``awcache ( AXIWPREF``aw.cache     ), // write command \
// write data channel \
.AXIPREF``wvalid  ( AXIWPREF``wvalid       ), // write data valid \
.AXIPREF``wready  ( AXIWPREF``wready       ), // write data accept \
.AXIPREF``wdata   ( AXIWPREF``wdata        ), // write data \
.AXIPREF``wstrb   ( AXIWPREF``wstrb        ), // write data strobe \
//.AXIPREF``wuser   ( AXIWPREF``wuser        ), // write data user field \
.AXIPREF``wlast   ( AXIWPREF``wlast        ), // write data last \
// write response channel \
.AXIPREF``bvalid  ( AXIWPREF``bvalid       ), // write response valid \
.AXIPREF``bready  ( AXIWPREF``bready       ), // write response accept \
.AXIPREF``bid     ( AXIWPREF``bid          ), // write response id \
//.AXIPREF``buser   ( AXIWPREF``buser        ), // read data user field \
.AXIPREF``bresp   ( AXIWPREF``bresp[1:0]   )  // write response \

`define AXISLV_STUB(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AXIPREF) \
assign   AXIPREF``arready  =  '0; \
assign   AXIPREF``rvalid   =  '0; \
assign   AXIPREF``rid      =  '0; \
assign   AXIPREF``rdata    =  '0; \
assign   AXIPREF``rresp    =  npu_axi_resp_t'(0); \
assign   AXIPREF``ruser    =  '0; \
assign   AXIPREF``rlast    =  '0; \
assign   AXIPREF``awready  =  '0; \
assign   AXIPREF``wready   =  '0; \
assign   AXIPREF``bvalid   =  '0; \
assign   AXIPREF``bid      =  '0; \
assign   AXIPREF``buser    =  '0; \
assign   AXIPREF``bresp    =  npu_axi_resp_t'(0)

`endif
