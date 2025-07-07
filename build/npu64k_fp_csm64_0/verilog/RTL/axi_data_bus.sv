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
// vcs -sverilog +incdir+../shared/RTL ../shared/RTL/npu_types.sv ../shared/RTL/npu_fifo.sv ../shared/RTL/npu_arb.sv ../shared/RTL/npu_axi_slice.sv ../shared/RTL/npu_axi_arc_bridge.sv ../shared/RTL/npu_axi_idconv.sv ../shared/RTL/npu_axi_mux.sv axi_data_bus.sv


`include "npu_defines.v"
`include "npu_axi_macros.svh"

module axi_data_bus 
  import npu_types::*;
  #(
    parameter int AXI_ARC_IDW = 2,
    parameter int AXI_SLV_IDW = 1,
    parameter int AXI_MST_IDW = 5,
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
   // L1 ARC master (64 bits DW, 4 bits ID_W)
   `AXISLV(AXI_ARC_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,cbu_mmio_axi_),
   // Meta data master (512 bits DW, 1'b0 ID)
   `AXISLV(AXI_SLV_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,metadata_data_axi_),
   // Feature Map master (512 bits DW, 1'b1 ID)
   `AXISLV(AXI_SLV_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,feature_map_data_axi_),
   // CLN Slave (512 bits DW, 2bits ID)
   `AXIMST(AXI_MST_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,cln_dev_data_axi_),
// spyglass enable_block W240
   //
   input logic clk,
   input logic rst_a,
   input logic test_mode
   );

  localparam int AXI_INT_IDW = AXI_SLV_IDW+$clog2(2);
  // local parameters
  localparam int CBU_IDX  = 0;
  localparam int FM_IDX   = 1;
  localparam int META_IDX = 2;

  // local wires
  `AXIWIRES(AXI_SLV_IDW,64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_cbu_);
  `AXIWIRESN(2,AXI_SLV_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_in_slv_);

  `AXIWIRESN(2,AXI_SLV_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slc_slv_);
  `AXIWIRES(AXI_INT_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mux_mst_);
  `AXIWIRES(AXI_MST_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_cln_);
  
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


  
  // reduce ID bits on CBU 
  npu_axi_idtrack
  #(
    .SIZE    ( 16          ),
    .AXISIDW ( AXI_ARC_IDW ),
    .AXIMIDW ( AXI_SLV_IDW ),
    .AXIDW   ( 64          ),
    .AXIAWUW ( AXIAWUW     ),
    .AXIWUW  ( AXIWUW      ),
    .AXIBUW  ( AXIBUW      ),
    .AXIARUW ( AXIARUW     ),
    .AXIRUW  ( AXIRUW      )
    )
  u_idconv_inst
    (
     // clock and reset
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     // AXI slave interface
     `AXIINST(axi_slv_,cbu_mmio_axi_),
     // AXI master interface
     `AXIINST(axi_mst_,axi_cbu_)
   );

  npu_axi_bridge
  #(
    .AXIIDW   ( AXI_SLV_IDW     ),
    .AXISDW   ( 64              ),
    .AXIMDW   ( VSIZE*64        ),
    .AXISAWUW ( AXIAWUW         ),
    .AXISWUW  ( AXIWUW          ),
    .AXISBUW  ( AXIBUW          ),
    .AXISARUW ( AXIARUW         ),
    .AXISRUW  ( AXIRUW          ),
    .AXIMAWUW ( AXIAWUW         ),
    .AXIMWUW  ( AXIWUW          ),
    .AXIMBUW  ( AXIBUW          ),
    .AXIMARUW ( AXIARUW         ),
    .AXIMRUW  ( AXIRUW          )
  )
  u_bridge_inst
  (
     .clk   ( clk   ),
     .rst_a ( rst_sync),
    `AXIINST(axi_slv_,axi_cbu_),
    `AXIINSTM(CBU_IDX,axi_mst_,axi_in_slv_)
  );

  //
  // Input assignment
  //
  `AXIASGN(FM_IDX,axi_in_slv_,feature_map_data_axi_);




  
  //
  // Input slices
  //
  for (genvar gs = 0; gs < 2; gs = gs + 1)
  begin : slc_slv_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( AXI_SLV_IDW ),
      .AXIDW        ( VSIZE*64    ),
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
     `AXIINSTM(gs, axi_slv_, axi_in_slv_),
     `AXIINSTM(gs, axi_mst_, axi_slc_slv_)
    );
  end : slc_slv_GEN
  
   npu_axi_matrix
  #(
    .NUMSLV  ( 2     ),
    .NUMMST  ( 1            ),
    .NUMAP   ( 1            ),  
    .AXIDW   ( VSIZE*64     ),
    .AXISIDW ( AXI_SLV_IDW  ),
    .AXIMIDW ( AXI_INT_IDW  ), 
    .AXIAWUW ( AXIAWUW      ),
    .AXIWUW  ( AXIWUW       ),
    .AXIBUW  ( AXIBUW       ),
    .AXIARUW ( AXIARUW      ),
    .AXIRUW  ( AXIRUW       )
  )
  u_mux_inst
  (
    .clk    ( clk      ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b0     ),
    .decslv ( '0       ),  
    `AXIINST(axi_slv_,axi_slc_slv_),
    `AXIINST(axi_mst_,axi_mux_mst_),
    .decbase('0                     ),
    .decsize('0                     ),
    .decmst ('0                     )
  );


  // reduce ID bits on slave interface to CLN
  `AXIASGNID(axi_mux_mst_,axi_cln_);
  assign axi_cln_arid     = axi_mux_mst_arid[AXI_INT_IDW-1:1];
  assign axi_cln_awid     = axi_mux_mst_awid[AXI_INT_IDW-1:1];
  assign axi_mux_mst_rid = {axi_cln_rid,1'b0};
  assign axi_mux_mst_bid = {axi_cln_bid,1'b0};

  //
  // Output slice
  //
  npu_axi_slice
    #(
      .AXIIDW       ( AXI_MST_IDW ),
      .AXIDW        ( VSIZE*64    ),
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
  u_slice_inst
    (
     // clock and reset
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     // AXI slave interface
     `AXIINST(axi_slv_,axi_cln_),
     // AXI master interface
     `AXIINST(axi_mst_,cln_dev_data_axi_)
    );
  
   `AXISLV_STUB(AXI_SLV_IDW,VSIZE*64,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,metadata_data_axi_);

endmodule : axi_data_bus
