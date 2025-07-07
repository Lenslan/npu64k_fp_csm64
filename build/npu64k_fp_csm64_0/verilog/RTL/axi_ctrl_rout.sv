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
// Top-level file for the Ctrl BUS (MMIO)
// Address map
//  dccm_dmi    { 0x00000000  0x0007ffff } 0
//  idma        { 0x00080000  0x00080fff } 1
//  odma        { 0x00081000  0x00081fff } 2
//  conv        { 0x00082000  0x00082fff } 3
//  activ       { 0x00083000  0x00083fff } 4
//  accum_mem   { 0x00100000  0x001fffff } 5
//  vec_mem     { 0x00200000  0x003fffff } 6
//
// vcs -sverilog +incdir+../shared/RTL ../shared/RTL/npu_types.sv ../shared/RTL/npu_fifo.sv ../shared/RTL/npu_arb.sv ../shared/RTL/npu_axi_slice.sv ../shared/RTL/npu_axi_mux.sv ../shared/RTL/npu_axi_demux.sv ../shared/RTL/npu_axi_matrix.sv axi_ctrl_rout.sv


`include "npu_defines.v"

`include "npu_axi_macros.svh"

module axi_ctrl_rout
  import npu_types::*;
  #(
    parameter int AXI_SLV_IDW = 1,
    parameter int AXI_ARC_IDW = 2,
    parameter int AXI_MST_IDW = 2+3,
    parameter int AXIAWUW     = 1,
    parameter int AXIWUW      = 1,
    parameter int AXIBUW      = 1,
    parameter int AXIARUW     = 1,
    parameter int AXIRUW      = 1
    )
  (
   //MMIO Master Output
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,idma_mmio_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,odma_mmio_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,conv_mmio_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,gten_mmio_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,vm_mmio_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,am_mmio_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,mmio_descr_axi_),
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,sfty_mmio_axi_),
   //MMIO Slave Input
// spyglass disable_block W240
//SMD:Intentional unconnect
//SJ :reserved region signal for future design
   `AXISLV(AXI_SLV_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,mmio_axi_),
   `AXISLV(AXI_ARC_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,lbu_mmio_axi_),
// spyglass enable_block W240
   // clock and reset
   input logic      clk,                    // clock, all logic clocked at posedge
   input logic      rst_a,                  // asynchronous reset, active high
   input logic      test_mode
   );
  // local parameters
  localparam int DCCM_IDX = 0;
  localparam int IDMA_IDX = 1;
  localparam int ODMA_IDX = 2;
  localparam int CONV_IDX = 3;
  localparam int GTOA_IDX = 4;
  localparam int SFTY_IDX = 5;
  localparam int AM_IDX   = 6;
  localparam int VM_IDX   = 7;
  localparam int NUMMST   = 8;

  //
  // Local wires
  //
  logic [NUMMST-1:0][NPU_AXI_ADDR_W-1:12] decbase;
  logic [NUMMST-1:0][NPU_AXI_ADDR_W-1:12] decsize;
  logic [NUMMST-1:0][NUMMST-1:0]          decmst;
  logic [1:0][NUMMST-1:0]                 decslv;
  `AXIWIRESN(2,AXI_ARC_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slc_slv_);
  `AXIWIRESN(2,AXI_ARC_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mat_slv_);
  `AXIWIRESN(NUMMST,AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mat_mst_);
  `AXIWIRESN(NUMMST,AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slc_mst_);

  //
  // Reset sync
  //
  logic rst_sync;
  npu_reset_ctrl 
  u_reset_sync_inst
  (
   .clk        ( clk       ),
   .rst_a      ( rst_a     ),
   .test_mode  ( test_mode ),
   .rst        ( rst_sync  )
  );
  
  
  //
  // Slice address map [39:12] and sparse routing
  //
  // Aperture 0: 0x00_0000      0x07_FFFF --> DCCM MMIO
  // Aperture 1: 0x08_0000      0x08_0FFF --> IDMA MMIO
  // Aperture 2: 0x08_1000      0x08_1FFF --> ODMA MMIO
  // Aperture 3: 0x08_2000      0x08_2FFF --> CONV MMIO
  // Aperture 4: 0x08_3000      0x08_3FFF --> GTOA MMIO
  // Aperture 5: 0x08_4000      0x08_5FFF --> SFTY MMIO
  // Aperture 6: 0x10_0000      0x1F_FFFF --> AM MMIO
  // Aperture 7: 0x20_0000      0x3F_FFFF --> VM MMIO
  // Reserved  : 0x40_0000      0xFF_FFFF --> L1 to access

  assign decbase[DCCM_IDX] = 28'h0000000;
  assign decsize[DCCM_IDX] = 28'h0000380;
  assign decmst[DCCM_IDX]  = unsigned'(1<<DCCM_IDX);
  assign decbase[IDMA_IDX] = 28'h0000080;
  assign decsize[IDMA_IDX] = 28'h00003ff;
  assign decmst[IDMA_IDX]  = unsigned'(1<<IDMA_IDX);
  assign decbase[ODMA_IDX] = 28'h0000081;
  assign decsize[ODMA_IDX] = 28'h00003ff;
  assign decmst[ODMA_IDX]  = unsigned'(1<<ODMA_IDX);
  assign decbase[CONV_IDX] = 28'h0000082;
  assign decsize[CONV_IDX] = 28'h00003ff;
  assign decmst[CONV_IDX]  = unsigned'(1<<CONV_IDX);
  assign decbase[GTOA_IDX] = 28'h0000083;
  assign decsize[GTOA_IDX] = 28'h00003ff;
  assign decmst[GTOA_IDX]  = unsigned'(1<<GTOA_IDX);
  assign decbase[SFTY_IDX] = 28'h0000084;
  assign decsize[SFTY_IDX] = 28'h00003fe;
  assign decmst[SFTY_IDX]  = unsigned'(1<<SFTY_IDX);
  assign decbase[AM_IDX]   = 28'h0000100;
  assign decsize[AM_IDX]   = 28'h0000300;
  assign decmst[AM_IDX]    = unsigned'(1<<AM_IDX);
  assign decbase[VM_IDX]   = 28'h0000200;
  assign decsize[VM_IDX]   = 28'h0000200;
  assign decmst[VM_IDX]    = unsigned'(1<<VM_IDX);
  assign decslv            = '1;
  
  
  //
  // Assign input interfaces
  //



  `AXIASGNNID(0,axi_slc_slv_,mmio_axi_);
  `AXIASGN(1,axi_slc_slv_,lbu_mmio_axi_);

  
  //
  // Input register slices
  //
  for (genvar gs = 0; gs < 2; gs = gs + 1)
  begin : slc_slv_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( AXI_ARC_IDW ),
      .AXIDW        ( 64          ),
      .AXIAWUW      ( AXIAWUW     ),
      .AXIWUW       ( AXIWUW      ),
      .AXIBUW       ( AXIBUW      ),
      .AXIARUW      ( AXIARUW     ),
      .AXIRUW       ( AXIRUW      ),
      .AWFIFO_DEPTH ( 1           ),
      .WFIFO_DEPTH  ( 2           ),
      .BFIFO_DEPTH  ( 1           ),
      .ARFIFO_DEPTH ( 1           ),
      .RFIFO_DEPTH  ( 2           )
    )
    u_slc_inst
    (
     .clk   ( clk   ),
     .rst_a ( rst_sync ),
     `AXIINSTM(gs, axi_slv_, axi_slc_slv_),
     `AXIINSTM(gs, axi_mst_, axi_mat_slv_)
    );
  end : slc_slv_GEN

  //
  // Switch matrix
  //
    npu_axi_matrix
  #(
    .NUMSLV  ( 2           ),
    .NUMMST  ( NUMMST      ),
    .NUMAP   ( NUMMST      ),
    .AXIDW   ( 64          ),
    .AXISIDW ( AXI_ARC_IDW ),
    .AXIMIDW ( AXI_MST_IDW ),
    .AXIAWUW ( AXIAWUW     ),
    .AXIWUW  ( AXIWUW      ),
    .AXIBUW  ( AXIBUW      ),
    .AXIARUW ( AXIARUW     ),
    .AXIRUW  ( AXIRUW      )
    )
  u_matrix_inst
  (
   .clk     ( clk     ),
   .rst_a   ( rst_sync ),
   .ptidx_a ( 2'b00 ),
   `AXIINST(axi_slv_,axi_mat_slv_),
   `AXIINST(axi_mst_,axi_mat_mst_),
   .decbase ( decbase ),
   .decsize ( decsize ),
   .decmst  ( decmst  ),
   .decslv  ( decslv  )
   );


  //
  // Output register slices
  //
  for (genvar gm = 0; gm < NUMMST; gm = gm + 1)
  begin : slc_mst_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( AXI_MST_IDW ),
      .AXIDW        ( 64          ),
      .AXIAWUW      ( AXIAWUW     ),
      .AXIWUW       ( AXIWUW      ),
      .AXIBUW       ( AXIBUW      ),
      .AXIARUW      ( AXIARUW     ),
      .AXIRUW       ( AXIRUW      ),
      .AWFIFO_DEPTH ( 1           ),
      .WFIFO_DEPTH  ( 2           ),
      .BFIFO_DEPTH  ( 1           ),
      .ARFIFO_DEPTH ( 1           ),
      .RFIFO_DEPTH  ( 2           )
    )
    u_slc_inst
    (
     .clk   ( clk   ),
     .rst_a ( rst_sync ),
     `AXIINSTM(gm, axi_slv_, axi_mat_mst_),
     `AXIINSTM(gm, axi_mst_, axi_slc_mst_)
    );
  end : slc_mst_GEN

  
  //
  // Assign input interfaces
  //
  `AXIASGM(IDMA_IDX,axi_slc_mst_,idma_mmio_axi_);
  `AXIASGM(ODMA_IDX,axi_slc_mst_,odma_mmio_axi_);
  `AXIASGM(CONV_IDX,axi_slc_mst_,conv_mmio_axi_);
  `AXIASGM(GTOA_IDX,axi_slc_mst_,gten_mmio_axi_);
  `AXIASGM(SFTY_IDX,axi_slc_mst_,sfty_mmio_axi_);
  `AXIASGM(VM_IDX,axi_slc_mst_,vm_mmio_axi_);
  `AXIASGM(AM_IDX,axi_slc_mst_,am_mmio_axi_);
  `AXIASGM(DCCM_IDX,axi_slc_mst_,mmio_descr_axi_);
  

endmodule : axi_ctrl_rout
