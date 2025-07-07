// -------------------------------------------------------------------------
//
// ------------------------------------------------------------------------------
//
// Copyright 2005 - 2020 Synopsys, INC.
//
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
//
// Component Name   : DW_axi_gs
// Component Version: 2.04a
// Release Type     : GA
// ------------------------------------------------------------------------------

//
// Release version :  2.04a
// File Version     :        $Revision: #21 $
// Revision: $Id: //dwh/DW_ocb/DW_axi_gs/amba_dev/src/DW_axi_gs.v#21 $
//
// -------------------------------------------------------------------------
//
// ABSTRACT:  AXI to Generic Interface (GIF) Gasket Top-level
//
// The Generic Slave Gasket design consists of three parts:
//   - a state machine that controls the data flow (sm),
//   - a datapath module that handles AXI to GIF requests (req),
//   - and a datapath module that handles GIF to AXI responses (resp).
//
//
// State machine (sm):
//                                |----|                           mread
// AXI Low-Power -----------------| sm |---------------------- GIF mwrite
//  Channel                       |____|                           mlast
//                                   |                             saccept
//                   <to/from req and resp data path>
//
//
// Request datapath (req):
//
//                                |----------|
// AXI WDATA ---------------------|fifo_wdata|---------------- GIF mdata
//  Channel                       |__________|                     mwstrb
//
//                                                                 maddr
// AXI AWADDR -|\   |-----------|  |---------|   /-----\           msize
//  Channel    | |__|exc_acc_mon|--|fifo_addr|---|logic|------ GIF mburst
//             | |  |___________|  |_________| | \-----/           mlen
// AXI ARADDR -|/                              |
//  Channel                                    |
//                                             |
//                                         ____|_____
// Response datapath (resp):              |          |
//                                   |--------| |--------|
//                                   |fifo_bid| |fifo_rid|
//                                   |--------| |--------|
//                                        |__________|
//                                             |                   mready
// AXI BRESP -\                    |---------| | /-----\           svalid
//  Channel    \___________________|fifo_resp|---|logic|------ GIF sdata
//             /                   |_________|   \-----/           sresp
// AXI RDATA -/
//  Channel
//
//
// Design Hierarchy
// ------------------------------------------------------
// - gsx                  Top-level
//    - sm                State machine
//    - lpfsm             Low power state machine
//    - req               Request channels (AXI to GIF)
//       - exclusive      Exclusive access monitor
//       - fifo_addr      Request buffer (writes and reads)
//       - fifo_wdata     Write Data buffer
//    - resp              Response channels (GIF to AXI)
//       - fifo_bid       Saves {id, exokay, exfail} of posted writes
//       - fifo_rid       Saves {id, len, exokay, exfail} of posted reads
//       - fifo_resp      Response buffer
//
// Internal signal naming conventions:
//
// Name           Meaning
// ----------------------------
// rd             Read
// wr             Write
// start          Start transaction
// advance        Advance beat (individual data transfer)
// f<signal>      Parsed data output of FIFO
// next_<signal>  DFF input
//
//-----------------------------------------------------------------------------
// Please refer to the databook for full details on the signals.
//
// These are found in the "Signal Description" section of the "Signals" chapter.
// There are details on the following
//   % Input Delays
//   % Output Delays
//   Any False Paths
//   Any Multicycle Paths
//   Any Asynchronous Signals

`include "arcsync_bus_gs_DW_axi_gs_all_includes.vh"

//mready signal is tied to 1'b1 in LITE mode.
//spyglass disable_block Topology_02
//SMD: No asynchronous pin to pin paths
//SJ : awvalid, bready, arvalid, rready, gclken, saccept, these signals are connected to output ports without being registered. This is as per the functionality requirement. So waiving this warning.

//==============================================================================
// Start License Usage
//==============================================================================
// Key Used   : DWC-AMBA-Fabric-Source (IP access)
//==============================================================================
// End License Usage
//==============================================================================

module arcsync_bus_gs_DW_axi_gs(/*AUTOARG*/
  // Outputs

  awready,
                 wready,
                 bid,
                 bresp,
                 bvalid,
                 arready,
                 rid,
                 rdata,
                 rresp,
                 rlast,
                 rvalid,
                 maddr,
                 mread,
                 mwrite,
                 msize,
                 mburst,
                 mlen,
                 mlast,
                 mdata,
                 mwstrb,
                 mready,
                 // Inputs
                 aclk,
                 aresetn,
                 awid,
                 awaddr,
                 awlen,
                 awsize,
                 awburst,
                 awlock,
                 awcache,
                 awprot,
                 awvalid,
                 wdata,
                 wstrb,
                 wlast,
                 wvalid,
                 bready,
                 arid,
                 araddr,
                 arlen,
                 arsize,
                 arburst,
                 arlock,
                 arcache,
                 arprot,
                 arvalid,
                 rready,
                 gclken,
                 saccept,
                 svalid,
                 sdata,
                 sresp
                 );
//spyglass enable_block Topology_02

// ----------------------------------------------------------------------------
// PORTS
// ----------------------------------------------------------------------------

  input                                       aclk;
  input                                       aresetn;
  input                                     gclken;

  //Write address channel
  input  [`ARCSYNC_REG_GS_ID-1:0] awid;
  input  [`ARCSYNC_REG_GS_AW-1:0] awaddr;
  input  [`ARCSYNC_REG_GS_BW-1:0] awlen;
  input  [2:0] awsize;
  input  [1:0] awburst;
  input  [`ARCSYNC_REG_AXI_LTW-1:0] awlock;
  //spyglass disable_block W240
  //SMD: An input has been declared but is not read
  //SJ : These signals are not actually required to be connected; They are not used
  //     and therefore are not connected internal to the component.
  input  [3:0] awcache;
  input  [2:0] awprot;
  input  wlast;
  //spyglass enable_block W240
  input  awvalid;
  output awready;
  //Write data channel
  input  [`ARCSYNC_REG_GS_DW-1:0] wdata;
  input  [`ARCSYNC_REG_GS_DW/8-1:0] wstrb;
  input  wvalid;
  output wready;
  //Write response channel
  output [`ARCSYNC_REG_GS_ID-1:0] bid;
  output [1:0] bresp;
  output bvalid;
  input  bready;
  //Read address channel
  input  [`ARCSYNC_REG_GS_ID-1:0] arid;
  input  [`ARCSYNC_REG_GS_AW-1:0] araddr;
  input  [`ARCSYNC_REG_GS_BW-1:0] arlen;
  input  [2:0] arsize;
  input  [1:0] arburst;
  input  [`ARCSYNC_REG_AXI_LTW-1:0] arlock;
  //spyglass disable_block W240
  //SMD: An input has been declared but is not read
  //SJ : These signals are not actually required to be connected; They are not used
  //     and therefore are not connected internal to the component.
  input  [3:0] arcache;
  input  [2:0] arprot;
  //spyglass enable_block W240
  input  arvalid;
  output arready;
  //Read data channel
  output [`ARCSYNC_REG_GS_ID-1:0] rid;
  output [`ARCSYNC_REG_GS_DW-1:0] rdata;
  output [1:0] rresp;
  output rlast;
  output rvalid;
  input  rready;
  //Low-power Channel

  //GENERIC SLAVE INTERFACE
  //Request Channel
  output [`ARCSYNC_REG_GS_AW-1:0] maddr;
  output mread;
  output mwrite;
  output [2:0] msize;
  output [1:0] mburst;
  output [`ARCSYNC_REG_GS_BW-1:0] mlen;
  output mlast;
  output [`ARCSYNC_REG_GS_DW-1:0] mdata;
  output [`ARCSYNC_REG_GS_DW/8-1:0] mwstrb;
  input  saccept;
  //Response Channel
  input  svalid;
  input  [1:0] sresp;
  input  [`ARCSYNC_REG_GS_DW-1:0] sdata;
  output mready;

  //ccx_module: DW_axi_gs_bcm57 ; This module is verified in a dedicated testbench and provided as fully verified
  //ccx_module: DW_axi_gs_bcm06 ; This module is verified in a dedicated testbench and provided as fully verified
  //ccx_module: DW_axi_gs_bcm65 ; This module is verified in a dedicated testbench and provided as fully verified
  //ccx_tgl: ; wdata ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.
  //ccx_tgl: ; rdata ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.
  //ccx_tgl: ; mdata ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.
  //ccx_tgl: ; awaddr ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.
  //ccx_tgl: ; araddr ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.
  //ccx_tgl: ; maddr ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.
  //ccx_tgl: ; sdata ; ; All bits of the bus can be covered by increasing randomisation. So there  is no functional issue due to this.

// --------------------------------------------------------------------
// INTERNAL SIGNALS
// --------------------------------------------------------------------

// req module valid signals (req to sm)
wire start_wr_valid, start_rd_valid, advance_wr_valid;

// resp module ready signals (resp to sm)
wire start_wr_ready, start_rd_ready;
wire advance_rd_ready;
wire resp_cactive;

// sm module control signals (sm to req/resp)
wire start_wr;
wire start_rd;
wire advance_wr, advance_rd;
wire req_last_accepted;
wire sm_high_pwr;

// data signals (req to resp)
wire [`ARCSYNC_REG_GS_ID-1:0] fid;
wire [`ARCSYNC_REG_GS_BW-1:0] flen;
wire fexokay, fexfail;

// --------------------------------------------------------------------
// DESIGN
// --------------------------------------------------------------------

// Instantiate state machine
arcsync_bus_gs_DW_axi_gs_sm

  sm (
  // AXI INTERFACE
  // Global
  .aclk(aclk)
      ,.aresetn(aresetn)
      ,// Low-power Channel
      .csysreq(1'b1)
      ,// GENERIC SLAVE INTERFACE
      // Global
      .gclken(gclken)
      ,// Request
      .mread(mread)
      ,.mwrite(mwrite)
      ,.mlast(mlast)
      ,.saccept(saccept)
      ,// INTERNAL CONNECTIONS
      // Inputs from req
      .start_wr_valid(start_wr_valid)
      ,.start_rd_valid(start_rd_valid)
      ,.advance_wr_valid(advance_wr_valid)
      ,//.exfail(fexfail),
      // Inputs from resp
      .start_wr_ready(start_wr_ready)
      ,.start_rd_ready(start_rd_ready)
      ,.advance_rd_ready(advance_rd_ready)
      ,.resp_cactive(resp_cactive)
      ,// Outputs to req/resp
      .start_wr(start_wr)
      ,.start_rd(start_rd)
      ,.advance_wr(advance_wr)
      ,.advance_rd(advance_rd)
      ,.req_last_accepted(req_last_accepted)
      ,.sm_high_pwr(sm_high_pwr)
      );

// Instantiate request module
arcsync_bus_gs_DW_axi_gs_req

  req (
  // AXI INTERFACE
  // Global
  .aclk(aclk),
       .aresetn(aresetn),
       // Write Address Channel
       .awid(awid),
       .awaddr(awaddr),
       .awlen(awlen),
       .awsize(awsize),
       .awburst(awburst),
       .awlock({1'b0,awlock}),
       .awvalid(awvalid),
       .awready(awready),
       // Write Data Channel
       .wdata(wdata),
       .wstrb(wstrb),
       .wvalid(wvalid),
       .wready(wready),
       // Read Address Channel
       .arid(arid),
       .araddr(araddr),
       .arlen(arlen),
       .arsize(arsize),
       .arburst(arburst),
       .arlock({1'b0,arlock}),
       .arvalid(arvalid),
       .arready(arready),
       // GENERIC SLAVE INTERFACE
       // Global
       .gclken(gclken),
       // Request
       .maddr(maddr),
       .msize(msize),
       .mburst(mburst),
       .mlen(mlen),
       .mlast(mlast),
       .mdata(mdata),
       .mwstrb(mwstrb),
       // INTERNAL CONNECTIONS
       // Inputs from sm
       //cg .start_wr(start_wr), .start_rd(start_rd),
       .advance_wr(advance_wr),
       .advance_rd(advance_rd),
       .req_last_accepted(req_last_accepted),
       // Outputs to sm
       .start_wr_valid(start_wr_valid),
       .start_rd_valid(start_rd_valid),
       .advance_wr_valid(advance_wr_valid),
       // Outputs to resp
       .fid(fid),
       .flen(flen),
       .fexokay(fexokay),
       .fexfail(fexfail),
       .sm_high_pwr(sm_high_pwr)
       );

// Instantiate response module
  //advance_rD_ready signal is tied to 1'b1/1'b0 in this configuration.
arcsync_bus_gs_DW_axi_gs_resp

  resp (
  // AXI INTERFACE
  // Global
  .aclk(aclk),
        .aresetn(aresetn),
        // Write Response Channel
        .bid(bid),
        .bresp(bresp),
        .bvalid(bvalid),
        .bready(bready),
        // Read Data Channel
        .rid(rid),
        .rdata(rdata),
        .rresp(rresp),
        .rlast(rlast),
        .rvalid(rvalid),
        .rready(rready),
        // GENERIC SLAVE INTERFACE
        // Global
        .gclken(gclken),
        // Response Channel
        .svalid(svalid),
        .sdata(sdata),
        .sresp(sresp),
        .mready(mready),
        // INTERNAL CONNECTIONS
        // Inputs from sm
        .start_wr(start_wr),
        .start_rd(start_rd),
        // Inputs from req
        .id(fid),
        .len(flen),
        .exokay(fexokay),
        .exfail(fexfail),
        // Outputs to sm
        .resp_cactive(resp_cactive),
        .advance_rd_ready(advance_rd_ready),
        .start_wr_ready(start_wr_ready),
        .start_rd_ready(start_rd_ready)
        );

endmodule
