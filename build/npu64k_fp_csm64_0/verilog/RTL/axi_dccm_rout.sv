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
// Top-level file for the DCCM BUS
//
// vcs -sverilog +incdir+../shared/RTL ../shared/RTL/npu_types.sv ../shared/RTL/npu_fifo.sv ../shared/RTL/npu_arb.sv ../shared/RTL/npu_axi_slice.sv ../shared/RTL/npu_axi_mux.sv axi_dccm_rout.sv


`include "npu_defines.v"

`include "npu_defines.v"
`include "npu_axi_macros.svh"

module axi_dccm_rout
  import npu_types::*;
  #(
    parameter int AXI_SLV_IDW = 3,
    parameter int AXI_MST_IDW = 3+3,
    parameter int AXIAWUW     = 1,
    parameter int AXIWUW      = 1,
    parameter int AXIBUW      = 1,
    parameter int AXIARUW     = 1,
    parameter int AXIRUW      = 1
    )
  (
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore axi macro, some of signals will not be used
   // DESCR Master Output
   `AXIMST(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,descr_axi_),            // AXI descriptor read/write
   // DESCR Slave Input
   `AXISLV(1,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,idma_descr_axi_),
   `AXISLV(1,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,odma_descr_axi_),
   `AXISLV(1,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,conv_descr_axi_),
   `AXISLV(1,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,gten_descr_axi_),
   `AXISLV(AXI_SLV_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,mmio_descr_axi_),
// spyglass enable_block W240
   //
   // clock and reset
   //
   input logic      clk,                    // clock, all logic clocked at posedge
   input logic      rst_a,                  // asynchronous reset, active high
   input logic      test_mode
   );
  // local parameters
  localparam int IDMA_IDX = 0;
  localparam int ODMA_IDX = 1;
  localparam int CONV_IDX = 2;
  localparam int GTOA_IDX = 3;
  localparam int MMIO_IDX = 4;


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
  // Local wires
  //
  `AXIWIRESN(5,AXI_SLV_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slc_slv_);
  `AXIWIRESN(5,AXI_SLV_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mux_slv_);
  `AXIWIRES(AXI_MST_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mux_mst_);
  

  //
  // Assign input interfaces
  //
  // fix ID to 0
  `AXIASGNNID(IDMA_IDX,axi_slc_slv_,idma_descr_axi_);
  `AXIASGNNID(ODMA_IDX,axi_slc_slv_,odma_descr_axi_);
  `AXIASGNNID(CONV_IDX,axi_slc_slv_,conv_descr_axi_);
  `AXIASGNNID(GTOA_IDX,axi_slc_slv_,gten_descr_axi_);
  // forward ID
  `AXIASGN(MMIO_IDX,axi_slc_slv_,mmio_descr_axi_);

  
  //
  // Input register slices
  //
  for (genvar gs = 0; gs < 5; gs = gs + 1)
  begin : slc_slv_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( AXI_SLV_IDW ),
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
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     `AXIINSTM(gs, axi_slv_, axi_slc_slv_),
     `AXIINSTM(gs, axi_mst_, axi_mux_slv_)
    );
  end : slc_slv_GEN

  //
  // AXI mux/arbiter
  //
  //npu_axi_mux
  //#(
  //  .NUMSLV  ( 5           ),
  //  .AXIDW   ( 64          ),
  //  .AXISIDW ( AXI_SLV_IDW ),
  //  .AXIMIDW ( AXI_MST_IDW ),
  //  .AXIAWUW ( AXIAWUW     ),
  //  .AXIWUW  ( AXIWUW      ),
  //  .AXIBUW  ( AXIBUW      ),
  //  .AXIARUW ( AXIARUW     ),
  //  .AXIRUW  ( AXIRUW      )
  //  )
  //u_mux_inst
  //(
  // .clk     ( clk     ),
  // .rst_a   ( rst_sync   ),
  // `AXIINST(axi_slv_,axi_mux_slv_),
  // `AXIINST(axi_mst_,axi_mux_mst_)
  // );

   npu_axi_matrix
  #(
    .NUMSLV  ( 5            ),
    .NUMMST  ( 1            ),
    .NUMAP   ( 1            ),  
    .AXIDW   ( 64           ),
    .AXISIDW ( AXI_SLV_IDW  ),
    .AXIMIDW ( AXI_MST_IDW  ), 
    .AXIAWUW ( AXIAWUW      ),
    .AXIWUW  ( AXIWUW       ),
    .AXIBUW  ( AXIBUW       ),
    .AXIARUW ( AXIARUW      ),
    .AXIRUW  ( AXIRUW       )
  )
  u_mux_inst
  (
    .clk    ( clk   ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00 ),
    .decslv ( '0    ),  
    `AXIINST(axi_slv_,axi_mux_slv_),
    `AXIINST(axi_mst_,axi_mux_mst_),
    .decbase('0                     ),
    .decsize('0                     ),
    .decmst ('0                     )
  );


  //
  // Output register slices
  //
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
   `AXIINST(axi_slv_,axi_mux_mst_),
   `AXIINST(axi_mst_,descr_axi_)
  );
  
endmodule : axi_dccm_rout
