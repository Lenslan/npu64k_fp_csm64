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
// Top-level demo file for the VM BUS
//
`include "npu_defines.v"
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"

// insert skid buffers on write commands
`define USE_WSKID

`include "npu_vm_ecc_macros.sv"

module vm_bus
  import npu_types::*;
  import npu_ecc_types::*;
  #(parameter AXI_SLV_IDW=3,
    parameter VM_RPORTS=((NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES+DMA_VM_LANES)+1),
    parameter VM_WPORTS=(VSIZE+GTOA_MPST_LANES+DMA_VM_LANES),
    parameter NUM_VM_BANKS=((VSIZE==8)?32:16)
   )
  (
   //
   // interfaces
   //
   // write request
   `VMWSLV(VM_WPORTS,nn_vm_wr_),
   // read request
   `VMRSLV(VM_RPORTS,nn_vm_rd_),

   // MMIO slave
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore axi macro, some of signals will not be used
   `AXISLV(AXI_SLV_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,vm_mmio_axi_),
// spyglass enable_block W240

   // muxed request
   `VMMST(NUM_VM_BANKS,vm_),
   // vm ecc 
   input  logic                     vm_prot_en,
   `VMMST_ECC(NUM_VM_BANKS,vm_),
   output logic                      vm_sb_err,
   output logic                      vm_db_err,

   // VM Init
   input  logic                        vm_init,
   output logic                        vm_init_end,

   //test mode
   input logic      test_mode, 
   //
   // clock and rst_a
   //
   input logic      clk,                   // clock, all logic clocked at posedge
   input logic      rst_a                  // asynchronous rst_a, active high
  );
  localparam INT_VM_RPORTS = VM_RPORTS+2; // add dmi r-m-w
  localparam INT_VM_WPORTS = VM_WPORTS+1;
  localparam VM_AW_SIZE    = 19;
  localparam int WWID = 16-$clog2(NUM_VM_BANKS)+ISIZE*9;

  logic rst;
 `VMRWIRES(INT_VM_RPORTS, int_nn_vm_rd_);
 `VMWWIRES(INT_VM_WPORTS, int_nn_vm_wr_);

 `VMRWIRES(1, dmi_nn_vm_rd_);
 `VMWWIRES(1, dmi_nn_vm_wr_);
 `VMRWIRES(1, rmw_nn_vm_rd_);
 `VMWWIRES(1, rmw_nn_vm_wr_);

  // Reset synchronizer
  npu_reset_ctrl 
  u_reset_ctrl_inst
  (
    .clk        ( clk       ),
    .rst_a      ( rst_a     ),
    .test_mode  ( test_mode ),
    .rst        ( rst       )
  );


  npu_axi2vm_bridge
  #(
    .D_WIDTH (64),
    .ID_WIDTH(AXI_SLV_IDW),
    .MEM_AW(VM_AW_SIZE)
  ) 
  u_npu_axi2vm_bridge
  (
       `AXIINST(axi_slv_,vm_mmio_axi_),
       `VMWINST_B(nn_vm_wr_,dmi_nn_vm_wr_),
       `VMRINST_B(nn_vm_rd_,dmi_nn_vm_rd_),
  
       .clk             (clk),
       .rst_a           (rst)
  );

   //
   // VM write data FIFO per bank and priority inversion after 4 cycles
   //
   logic       [NUM_VM_BANKS-1:0]           wfifo_wvalid;
   logic       [NUM_VM_BANKS-1:0]           wfifo_waccept;
   logic       [NUM_VM_BANKS-1:0][WWID-1:0] wfifo_wdata;
   logic       [NUM_VM_BANKS-1:0]           wfifo_rvalid;
   logic       [NUM_VM_BANKS-1:0]           wfifo_raccept;
   logic       [NUM_VM_BANKS-1:0][WWID-1:0] wfifo_rdata;
   logic       [NUM_VM_BANKS-1:0]           wfifo_prio;

  //
  // Write data FIFO per bank and priority inversion after 4 cycles
  //
  for (genvar gb = 0; gb < NUM_VM_BANKS; gb++)
  begin : wbuf_GEN
    //
    // Buffer
    //
    npu_fifo 
    #(
      .SIZE   ( 2    ),
      .DWIDTH ( WWID )
    ) 
    u_wfifo_inst
    (
     .clk          ( clk               ),
     .rst_a        ( rst               ),
     .valid_write  ( wfifo_wvalid[gb]  ),
     .accept_write ( wfifo_waccept[gb] ),
     .data_write   ( wfifo_wdata[gb]   ),
     .valid_read   ( wfifo_rvalid[gb]  ),
     .accept_read  ( wfifo_raccept[gb] ),
     .data_read    ( wfifo_rdata[gb]   )
     );

    npu_wfifo_prio_ctrl
    u_wfifo_prio_ctrl_inst
    (
     .clk           ( clk               ),
     .rst_a         ( rst               ),
     .wfifo_raccept ( wfifo_raccept[gb] ),
     .wfifo_rvalid  ( wfifo_rvalid[gb]  ),
     .wfifo_prio    ( wfifo_prio[gb]    )
    );
  end : wbuf_GEN


  // Arbitrate the VM banks
  vm_mux
  #(
    .VM_RPORTS(INT_VM_RPORTS),
    .VM_WPORTS(INT_VM_WPORTS),
    .NUM_VM_BANKS(NUM_VM_BANKS),
    .WWID(WWID)
  ) 
  u_vm_mux
  (

    .clk                 (clk),
    .rst_a               (rst),
    .test_mode           (test_mode),
    .vm_init             (vm_init),
    .vm_init_end         (vm_init_end),
    .wfifo_wvalid        (wfifo_wvalid),
    .wfifo_waccept       (wfifo_waccept),
    .wfifo_wdata         (wfifo_wdata),
    .wfifo_rvalid        (wfifo_rvalid),
    .wfifo_raccept       (wfifo_raccept),
    .wfifo_rdata         (wfifo_rdata),
    .wfifo_prio          (wfifo_prio),
    `VMWINST_B(nn_vm_wr_,int_nn_vm_wr_),
    `VMRINST_B(nn_vm_rd_,int_nn_vm_rd_),
    .vm_prot_en          (vm_prot_en),
    `VMINST_ECC          (vm_,vm_),
    .vm_sb_err           (vm_sb_err),
    .vm_db_err           (vm_db_err),
    `VMINST(vm_,vm_)
  );

  // Connection
 `ifdef USE_RSKID
  // Use skid buffers on read command input
  genvar gvr_i;
  for (gvr_i = 0; gvr_i < VM_RPORTS; gvr_i = gvr_i + 1)
  begin: read_port_buffer_GEN
    npu_skid
    #(
      .W (16)
    )
    u_read_skid_inst
    (
      .clk          ( clk                           ),
      .rst_a        ( rst                           ),
      .in_valid     ( nn_vm_rd_cmd_valid[gvr_i]     ),
      .in_accept    ( nn_vm_rd_cmd_accept[gvr_i]    ),
      .in_data      ( nn_vm_rd_cmd_addr[gvr_i]      ),
      .int_valid    (                               ), // intentionally left unconnected
      .out_valid    ( int_nn_vm_rd_cmd_valid[gvr_i] ),
      .out_accept   ( int_nn_vm_rd_cmd_accept[gvr_i]),
      .out_data     ( int_nn_vm_rd_cmd_addr[gvr_i]  )
    );  
  end : read_port_buffer_GEN
  
  npu_skid
  #(
    .W (16)
   )
   u_dmi_read_slice_int_inst
   (
     .clk          ( clk                               ),
     .rst_a        ( rst                               ),
     .in_valid     ( dmi_nn_vm_rd_cmd_valid            ),
     .in_accept    ( dmi_nn_vm_rd_cmd_accept           ),
     .in_data      ( dmi_nn_vm_rd_cmd_addr             ),
     .int_valid    (                                   ), // intentionally left unconnected
     .out_valid    ( int_nn_vm_rd_cmd_valid[VM_RPORTS] ),
     .out_accept   ( int_nn_vm_rd_cmd_accept[VM_RPORTS]),
     .out_data     ( int_nn_vm_rd_cmd_addr[VM_RPORTS]  )
   );
  
  npu_skid
  #(
    .W (16)
   )
   u_dmi_rmw_read_skid_inst
   (
     .clk          ( clk                  ),
     .rst_a        ( rst                ),
     .in_valid     ( rmw_nn_vm_rd_cmd_valid            ),
     .in_accept    ( rmw_nn_vm_rd_cmd_accept           ),
     .in_data      ( rmw_nn_vm_rd_cmd_addr             ),
     .int_valid    (                                   ), // intentionally left unconnected
     .out_valid    ( int_nn_vm_rd_cmd_valid[VM_RPORTS+1] ),
     .out_accept   ( int_nn_vm_rd_cmd_accept[VM_RPORTS+1]),
     .out_data     ( int_nn_vm_rd_cmd_addr[VM_RPORTS+1] )
   );  
`else // !`ifdef USE_RSKID
  // 1 deep fifo on read command, limits throughput to 1 per 2 cycles
  logic dmit_nn_vm_rd_cmd_valid;
  logic dmit_nn_vm_rd_cmd_accept;
  logic [15:0] dmit_nn_vm_rd_cmd_addr;
  npu_fifo
  #(
    .SIZE   ( 1    ),
    .DWIDTH ( 16   ),
    .FRCVAL ( 1'b0 ),
    .FRCACC ( 1'b0 )
   )
   u_dmi_read_fifo_inst
   (
     .clk          ( clk                               ),
     .rst_a        ( rst                               ),
     .valid_write  ( dmi_nn_vm_rd_cmd_valid            ),
     .accept_write ( dmi_nn_vm_rd_cmd_accept           ),
     .data_write   ( dmi_nn_vm_rd_cmd_addr             ),
     .valid_read   ( dmit_nn_vm_rd_cmd_valid           ),
     .accept_read  ( dmit_nn_vm_rd_cmd_accept          ),
     .data_read    ( dmit_nn_vm_rd_cmd_addr            )
   );


  logic rmwt_nn_vm_rd_cmd_valid;
  logic rmwt_nn_vm_rd_cmd_accept;
  vm_addr_t rmwt_nn_vm_rd_cmd_addr;
  npu_fifo
  #(
    .SIZE   ( 1    ),
    .DWIDTH ( 16 ),
    .FRCVAL ( 1'b0 ),
    .FRCACC ( 1'b0 )
   )
   u_rmw_read_fifo_inst
   (
     .clk          ( clk                               ),
     .rst_a        ( rst                               ),
     .valid_write  ( rmw_nn_vm_rd_cmd_valid            ),
     .accept_write ( rmw_nn_vm_rd_cmd_accept           ),
     .data_write   ( rmw_nn_vm_rd_cmd_addr             ),
     .valid_read   ( rmwt_nn_vm_rd_cmd_valid           ),
     .accept_read  ( rmwt_nn_vm_rd_cmd_accept          ),
     .data_read    ( rmwt_nn_vm_rd_cmd_addr            )
   );

  // no read skid buffers
  assign int_nn_vm_rd_cmd_valid                        = {rmwt_nn_vm_rd_cmd_valid,dmit_nn_vm_rd_cmd_valid,nn_vm_rd_cmd_valid};
  assign {rmwt_nn_vm_rd_cmd_accept,dmit_nn_vm_rd_cmd_accept,nn_vm_rd_cmd_accept} = int_nn_vm_rd_cmd_accept;
  assign int_nn_vm_rd_cmd_addr                         = {rmwt_nn_vm_rd_cmd_addr,dmit_nn_vm_rd_cmd_addr,nn_vm_rd_cmd_addr};
`endif // !`ifdef USE_RSKID

`ifdef USE_WSKID
  // Use skid buffers on write command input and FIFO for DMI port
  genvar gvw_i;
  for (gvw_i = 0; gvw_i < VM_WPORTS; gvw_i = gvw_i + 1)
  begin: write_port_buffer_GEN
    npu_skid
    #(
      .W (ISIZE*PIX_W+ISIZE+16)
    )
    u_write_skid_inst
    (
      .clk          ( clk                           ),
      .rst_a        ( rst                           ),
      .in_valid     ( nn_vm_wr_cmd_valid[gvw_i]     ),
      .in_accept    ( nn_vm_wr_cmd_accept[gvw_i]    ),
      .in_data      ( {nn_vm_wr_cmd_addr[gvw_i],nn_vm_wr_wdata[gvw_i],nn_vm_wr_wstrb[gvw_i]}),
      .int_valid    (                               ), // intentionally left unconnected
      .out_valid    ( int_nn_vm_wr_cmd_valid[gvw_i] ),
      .out_accept   ( int_nn_vm_wr_cmd_accept[gvw_i]),
      .out_data     ( {int_nn_vm_wr_cmd_addr[gvw_i],int_nn_vm_wr_wdata[gvw_i],int_nn_vm_wr_wstrb[gvw_i]})
    );
  end : write_port_buffer_GEN

  npu_fifo
  #(
    .SIZE   ( 1                    ),
    .DWIDTH ( ISIZE*PIX_W+ISIZE+16 ),
    .FRCVAL ( 1'b0                 ),
    .FRCACC ( 1'b0                 )
  )
  u_dmi_write_fifo_inst
  (
    .clk          ( clk                                ),
    .rst_a        ( rst                                ),
     .valid_write  ( rmw_nn_vm_wr_cmd_valid             ),
     .accept_write ( rmw_nn_vm_wr_cmd_accept            ), 
     .data_write   ( {rmw_nn_vm_wr_cmd_addr,
                      rmw_nn_vm_wr_wdata,
                      rmw_nn_vm_wr_wstrb
                    }), 
    .valid_read   ( int_nn_vm_wr_cmd_valid[VM_WPORTS]  ),
    .accept_read  ( int_nn_vm_wr_cmd_accept[VM_WPORTS] ),
    .data_read    ( {int_nn_vm_wr_cmd_addr[VM_WPORTS],
                     int_nn_vm_wr_wdata[VM_WPORTS],
                     int_nn_vm_wr_wstrb[VM_WPORTS]
                    }));

`else // !`ifdef USE_WSKID
  // no write skid buffers
  assign int_nn_vm_wr_cmd_valid                        = {rmw_nn_vm_wr_cmd_valid,nn_vm_wr_cmd_valid};
  assign {rmw_nn_vm_wr_cmd_accept,nn_vm_wr_cmd_accept} = int_nn_vm_wr_cmd_accept;
  assign int_nn_vm_wr_cmd_addr                         = {rmw_nn_vm_wr_cmd_addr,nn_vm_wr_cmd_addr};
  assign int_nn_vm_wr_wdata                            = {rmw_nn_vm_wr_wdata,nn_vm_wr_wdata};
  assign int_nn_vm_wr_wstrb                            = {rmw_nn_vm_wr_wstrb,nn_vm_wr_wstrb};
`endif // !`ifdef USE_WSKID

  assign nn_vm_rd_rdata      = int_nn_vm_rd_rdata[VM_RPORTS-1:0];
  assign nn_vm_rd_rvalid     = int_nn_vm_rd_rvalid[VM_RPORTS-1:0];
  assign dmi_nn_vm_rd_rdata  = int_nn_vm_rd_rdata[VM_RPORTS];
  assign dmi_nn_vm_rd_rvalid = int_nn_vm_rd_rvalid[VM_RPORTS];

  //
  // VM dmi r-m-w instance
  //
  npu_vm_rmw    
  u_npu_vm_dmi_rmw
  (
  `VMWINST_B(in_wr_,dmi_nn_vm_wr_),      // VM write from dmi
//`if(`NPU_SAFETY_LEVEL>0)//{
//     .in_wr_wdata_edc  (nn_vm_wr_wdata_edc),
//`endif//}NPU_SAFETY_LEVEL
  `VMWINST_B(out_wr_,rmw_nn_vm_wr_),     // VM write to vm_mux
  `VMRINST_B(rd_,rmw_nn_vm_rd_),         // VM read from vm_mux
  .clk       (clk       ),
  .rst_a     (rst       ) 
  );

  assign rmw_nn_vm_rd_rdata  = int_nn_vm_rd_rdata[VM_RPORTS+1];
  assign rmw_nn_vm_rd_rvalid = int_nn_vm_rd_rvalid[VM_RPORTS+1];

endmodule
`undef USE_WSKID
