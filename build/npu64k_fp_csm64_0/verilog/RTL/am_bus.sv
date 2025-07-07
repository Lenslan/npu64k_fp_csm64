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
// Top-level file for the AM BUS
//
`include "npu_defines.v"
 
`include "npu_defines.v"
`include "npu_axi_macros.svh"
`include "npu_am_macros.svh"

`define USE_WSKID

`include "npu_am_ecc_macros.sv"

module am_bus
  import npu_types::*;
  import npu_ecc_types::*;
  #(
    parameter int AXI_SLV_IDW = 3,
    parameter int AM_RPORTS = 5,
    parameter int AM_WPORTS = 4,
    parameter int NUM_AM_BANKS = 2
   )
  (
   //
   // interfaces
   //
   // write request
   `AMWSLV(nn_am_wr_,AM_WPORTS),

   // read request
   `AMRSLV(nn_am_rd_,AM_RPORTS),

   // MMIO slave
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore axi macro, some of signals will not be used 
   `AXISLV(AXI_SLV_IDW,64,1,1,1,1,1,am_mmio_axi_),
// spyglass enable_block W240

   // MUXED request
   `AMMST_MSK(NUM_AM_BANKS,am_),
   // AM ecc 
   input  logic                     am_prot_en,
   `AMMST_ECC(NUM_AM_BANKS,am_),
   output logic                      am_sb_err,
   output logic                      am_db_err,

   // AM Init
   input  logic                        am_init,
   output logic                        am_init_end,
   //
   // clock and reset
   //
   input logic      clk,                    // clock, all logic clocked at posedge
   input logic      rst_a,                  // asynchronous reset, active high
   input logic      test_mode
);

  localparam INT_AM_RPORTS = AM_RPORTS+1;
  localparam INT_AM_WPORTS = AM_WPORTS+1;
  localparam AM_AW_SIZE    = 17;
  logic rst;
  `AMRWIRES(int_nn_am_rd_, INT_AM_RPORTS);
  `AMWWIRES_MSK(int_nn_am_wr_, INT_AM_WPORTS);

  `AMRWIRES(dmi_nn_am_rd_, 1);
  `AMWWIRES_MSK(dmi_nn_am_wr_, 1); 
  
  
  npu_axi2am_bridge
  #(
    .D_WIDTH (64),
    .MEM_AW(AM_AW_SIZE),
    .ID_WIDTH(AXI_SLV_IDW) 
  ) 
  u_npu_axi2am_bridge
  (
    `AXIINST(axi_slv_,am_mmio_axi_),
    `AMWINST_B_MSK(nn_am_wr_,dmi_nn_am_wr_),
    `AMRINST_B(nn_am_rd_,dmi_nn_am_rd_),

    .clk             (clk),
    .rst_a           (rst)
  );

  // Reset synchronizer
  npu_reset_ctrl 
  u_reset_ctrl_inst
  (
    .clk        ( clk       ),
    .rst_a      ( rst_a     ),
    .test_mode  ( test_mode ),
    .rst        ( rst       )
  );

  // bank arbitration
  am_mux 
  #(
    .AM_RPORTS(INT_AM_RPORTS),
    .AM_WPORTS(INT_AM_WPORTS),
    .NUM_AM_BANKS(2)
  ) 
  u_am_mux
  (
    .clk                 (clk),
    .rst_a               (rst),
    .test_mode           (test_mode),
    .am_init             (am_init),
    .am_init_end         (am_init_end),
    `AMWINST_B_MSK(nn_am_wr_,int_nn_am_wr_),
    `AMRINST_B(nn_am_rd_,int_nn_am_rd_),
     .am_prot_en          (am_prot_en),
     `AMINST_ECC          (am_,am_),
      .am_sb_err           (am_sb_err),
      .am_db_err           (am_db_err),
    `AMINST_MSK(am_,am_)
  );

//Connection
`ifdef USE_RSKID
  // Insert skid buffers on read ports
  genvar gvr_i;
  for (gvr_i = 0; gvr_i < AM_RPORTS; gvr_i = gvr_i + 1)
  begin: read_port_buffer_GEN
    npu_skid
    #(
      .W (10)
    )
    u_read_skid_inst
    (
      .clk          ( clk                           ),
      .rst_a        ( rst                           ),
      .in_valid     ( nn_am_rd_cmd_valid[gvr_i]     ),
      .in_accept    ( nn_am_rd_cmd_accept[gvr_i]    ),
      .in_data      ( nn_am_rd_cmd_addr[gvr_i]      ),
      .int_valid    (                               ), // intentionally left unconnected
      .out_valid    ( int_nn_am_rd_cmd_valid[gvr_i] ),
      .out_accept   ( int_nn_am_rd_cmd_accept[gvr_i]),
      .out_data     ( int_nn_am_rd_cmd_addr[gvr_i]  )
    );  
  end : read_port_buffer_GEN

  npu_skid
  #(
    .W (10)
  )
  u_dmi_read_skid_inst
  (
    .clk          ( clk                               ),
    .rst_a        ( rst                               ),
    .in_valid     ( dmi_nn_am_rd_cmd_valid            ),
    .in_accept    ( dmi_nn_am_rd_cmd_accept           ),
    .in_data      ( dmi_nn_am_rd_cmd_addr             ),
    .int_valid    (                                   ), // intentionally left unconnected
    .out_valid    ( int_nn_am_rd_cmd_valid[AM_RPORTS] ),
    .out_accept   ( int_nn_am_rd_cmd_accept[AM_RPORTS]),
    .out_data     ( int_nn_am_rd_cmd_addr[AM_RPORTS]  )
  );  
`else
  // 1 deep fifo on read command, limits throughput to 1 per 2 cycles
  logic dmit_nn_am_rd_cmd_valid;
  logic dmit_nn_am_rd_cmd_accept;
  logic [9:0] dmit_nn_am_rd_cmd_addr;
  npu_fifo
  #(
    .SIZE   ( 1    ),
    .DWIDTH ( 10   ),
    .FRCVAL ( 1'b0 ),
    .FRCACC ( 1'b0 )
  )
  u_dmi_read_fifo_inst
  (
    .clk          ( clk                               ),
    .rst_a        ( rst                               ),
    .valid_write  ( dmi_nn_am_rd_cmd_valid            ),
    .accept_write ( dmi_nn_am_rd_cmd_accept           ),
    .data_write   ( dmi_nn_am_rd_cmd_addr             ),
    .valid_read   ( dmit_nn_am_rd_cmd_valid           ),
    .accept_read  ( dmit_nn_am_rd_cmd_accept          ),
    .data_read    ( dmit_nn_am_rd_cmd_addr            )
  );
  // no skid buffer on read other ports
  assign int_nn_am_rd_cmd_valid = {dmit_nn_am_rd_cmd_valid,nn_am_rd_cmd_valid};
  assign {dmit_nn_am_rd_cmd_accept,nn_am_rd_cmd_accept} = int_nn_am_rd_cmd_accept;
  assign int_nn_am_rd_cmd_addr  = {dmit_nn_am_rd_cmd_addr,nn_am_rd_cmd_addr};
`endif

`ifdef USE_WSKID
  // Insert skid buffers on write ports
  genvar gvw_i;
  for(gvw_i = 0; gvw_i < AM_WPORTS; gvw_i = gvw_i + 1)
  begin: write_port_buffer_GEN
    assign int_nn_am_wr_wstrb[gvw_i] = 128'hffffffffffffffffffffffffffffffff;


    // skid buffer on write data
    npu_skid
      #(
        .W ( ACC_W*ISIZE*VSIZE+10    ),
        .D ( (gvw_i == 0) ? 2 : 1) // port 0 has deeper skid buffer
        )
    u_amwr_skid_inst
      (
       .clk          ( clk          ),
       .rst_a        ( rst          ),
       .in_valid     ( nn_am_wr_cmd_valid[gvw_i]     ),
       .in_accept    ( nn_am_wr_cmd_accept[gvw_i]    ),
       .in_data      ( {nn_am_wr_cmd_addr[gvw_i],nn_am_wr_wdata[gvw_i]}  ),
       .int_valid    (                                   ), // intentionally left unconnected
       .out_valid    ( int_nn_am_wr_cmd_valid[gvw_i]     ),
       .out_accept   ( int_nn_am_wr_cmd_accept[gvw_i]    ),
       .out_data     (  {int_nn_am_wr_cmd_addr[gvw_i],int_nn_am_wr_wdata[gvw_i]}  )
       );

    assign nn_am_wr_aw_consumed[gvw_i] = int_nn_am_wr_cmd_valid[gvw_i] & int_nn_am_wr_cmd_accept[gvw_i];
  end : write_port_buffer_GEN

  // FIFO on DMI write port, 1 transfer in 2 cycles
  npu_fifo
  #(
    .SIZE   ( 1                                ),
    .DWIDTH ( ACC_W*ISIZE*VSIZE+10+ISIZE*VSIZE ),
    .FRCVAL ( 1'b0                             ),
    .FRCACC ( 1'b0                             )
   )
   u_dmi_write_fifo_inst
   (
     .clk          ( clk                                                                                           ),
     .rst_a        ( rst                                                                                           ),
     .valid_write  ( dmi_nn_am_wr_cmd_valid                                                                        ),
     .accept_write ( dmi_nn_am_wr_cmd_accept                                                                       ),
     .data_write   ( {dmi_nn_am_wr_cmd_addr,dmi_nn_am_wr_wdata,dmi_nn_am_wr_wstrb}                                 ),
     .valid_read   ( int_nn_am_wr_cmd_valid[AM_WPORTS]                                                             ),
     .accept_read  ( int_nn_am_wr_cmd_accept[AM_WPORTS]                                                            ),
     .data_read    ( {int_nn_am_wr_cmd_addr[AM_WPORTS],int_nn_am_wr_wdata[AM_WPORTS],int_nn_am_wr_wstrb[AM_WPORTS]})
   );


`else
  // no skid buffer on write ports
  assign int_nn_am_wr_cmd_valid = {dmi_nn_am_wr_cmd_valid,nn_am_wr_cmd_valid};
  assign {dmi_nn_am_wr_cmd_accept,nn_am_wr_cmd_accept} = int_nn_am_wr_cmd_accept;
  assign int_nn_am_wr_cmd_addr  = {dmi_nn_am_wr_cmd_addr,nn_am_wr_cmd_addr};
  assign int_nn_am_wr_wdata     = {dmi_nn_am_wr_wdata,nn_am_wr_wdata};
  assign int_nn_am_wr_wstrb     = {dmi_nn_am_wr_wstrb,nn_am_wr_wstrb};
`endif

  assign nn_am_rd_rdata      = int_nn_am_rd_rdata[AM_RPORTS-1:0];
  assign nn_am_rd_rvalid     = int_nn_am_rd_rvalid[AM_RPORTS-1:0];
  assign dmi_nn_am_rd_rdata  = int_nn_am_rd_rdata[AM_RPORTS];
  assign dmi_nn_am_rd_rvalid = int_nn_am_rd_rvalid[AM_RPORTS];


endmodule
`undef USE_WSKID
