
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

// Stub AXI when clock is not enabled, return error to master 



`include "npu_axi_macros.svh"


module npu_axi_inj_stall
  import npu_types::*;
  #(
    parameter int AXIIDW       = 4,
    parameter int AXIAW        = 32,
    parameter int AXIDW        = 128,
    parameter int AXIAWUW      = 1,
    parameter int AXIWUW       = 1,
    parameter int AXIBUW       = 1,
    parameter int AXIARUW      = 1,
    parameter int AXIRUW       = 1,
    parameter int AXIRGN       = 4,
    parameter int AXILEN       = 4
  )
  (
// spyglass disable_block W240
//SMD:Input clk,rst_a not read
//SJ :Will be read when AXI_WR_CMD_INJECT_STALL
   // clock and reset
   input  logic clk,
   input  logic rst_a,
// spyglass enable_block W240

   // AXI Slave
   input  logic                  axi_slv_arvalid, // read command valid
   output logic                  axi_slv_arready, // read command accept
   input  logic    [AXIIDW-1:0]  axi_slv_arid,    // read command ID
   input  logic    [AXIARUW-1:0] axi_slv_aruser,  // read command user field
   input  logic    [AXIAW-1:0]   axi_slv_araddr  ,// read command
   input  logic    [3:0]         axi_slv_arcache ,// read command
   input  logic    [2:0]         axi_slv_arprot  ,// read command
   input  logic    [0:0]         axi_slv_arlock  ,// read command
   input  logic    [1:0]         axi_slv_arburst ,// read command
   input  logic    [AXILEN-1:0]  axi_slv_arlen   ,// read command
   input  logic    [2:0]         axi_slv_arsize  ,// read command
   input  logic    [AXIRGN-1:0]  axi_slv_arregion,// read command

   output logic                  axi_slv_rvalid,  // read data valid
   input  logic                  axi_slv_rready,  // read data accept
   output logic    [AXIIDW-1:0]  axi_slv_rid,     // read data id
   output logic    [AXIDW-1:0]   axi_slv_rdata,   // read data
   output logic    [1:0]         axi_slv_rresp,   // read response
   output logic    [AXIRUW-1:0]  axi_slv_ruser,   // read data user field
   output logic                  axi_slv_rlast,   // read last

   input  logic                  axi_slv_awvalid, // write command valid
   output logic                  axi_slv_awready, // write command accept
   input  logic    [AXIIDW-1:0]  axi_slv_awid,    // write command ID
   input  logic    [AXIAWUW-1:0] axi_slv_awuser,  // write command user field
   input  logic    [AXIAW-1:0]   axi_slv_awaddr  ,// write command
   input  logic    [3:0]         axi_slv_awcache ,// write command
   input  logic    [2:0]         axi_slv_awprot  ,// write command
   input  logic    [0:0]         axi_slv_awlock  ,// write command
   input  logic    [1:0]         axi_slv_awburst ,// write command
   input  logic    [AXILEN-1:0]  axi_slv_awlen   ,// write command
   input  logic    [2:0]         axi_slv_awsize  ,// write command
   input  logic    [AXIRGN-1:0]  axi_slv_awregion,// write command

   input  logic                  axi_slv_wvalid,  // write data valid
   output logic                  axi_slv_wready,  // write data accept
   input  logic    [AXIDW-1:0]   axi_slv_wdata,   // write data
   input  logic    [AXIDW/8-1:0] axi_slv_wstrb,   // write data strobe
   input  logic    [AXIWUW-1:0]  axi_slv_wuser,   // write data user field
   input  logic                  axi_slv_wlast,   // write data last

   output logic                  axi_slv_bvalid,  // write response valid
   input  logic                  axi_slv_bready,  // write response accept
   output logic    [AXIIDW-1:0]  axi_slv_bid,     // write response id
   output logic    [AXIBUW-1:0]  axi_slv_buser,   // write response user field
   output logic    [1:0]         axi_slv_bresp,   // write response

   // AXI Master
   output logic                  axi_mst_arvalid, // read command valid
   input  logic                  axi_mst_arready, // read command accept
   output logic    [AXIIDW-1:0]  axi_mst_arid,    // read command ID
   output logic    [AXIARUW-1:0] axi_mst_aruser,  // read command user field
   output logic    [AXIAW-1:0]   axi_mst_araddr  ,// read command
   output logic    [3:0]         axi_mst_arcache ,// read command
   output logic    [2:0]         axi_mst_arprot  ,// read command
   output logic    [0:0]         axi_mst_arlock  ,// read command
   output logic    [1:0]         axi_mst_arburst ,// read command
   output logic    [AXILEN-1:0]  axi_mst_arlen   ,// read command
   output logic    [2:0]         axi_mst_arsize  ,// read command
   output logic    [AXIRGN-1:0]  axi_mst_arregion,// read command

   input  logic                  axi_mst_rvalid,  // read data valid
   output logic                  axi_mst_rready,  // read data accept
   input  logic    [AXIIDW-1:0]  axi_mst_rid,     // read data id
   input  logic    [AXIDW-1:0]   axi_mst_rdata,   // read data
   input  logic    [1:0]         axi_mst_rresp,   // read response
   input  logic    [AXIRUW-1:0]  axi_mst_ruser,   // read data user field
   input  logic                  axi_mst_rlast,   // read last

   output logic                  axi_mst_awvalid, // write command valid
   input  logic                  axi_mst_awready, // write command accept
   output logic    [AXIIDW-1:0]  axi_mst_awid,    // write command ID
   output logic    [AXIAWUW-1:0] axi_mst_awuser,  // write command user field
   output logic    [AXIAW-1:0]   axi_mst_awaddr  ,// write command
   output logic    [3:0]         axi_mst_awcache ,// write command
   output logic    [2:0]         axi_mst_awprot  ,// write command
   output logic    [0:0]         axi_mst_awlock  ,// write command
   output logic    [1:0]         axi_mst_awburst ,// write command
   output logic    [AXILEN-1:0]  axi_mst_awlen   ,// write command
   output logic    [2:0]         axi_mst_awsize  ,// write command
   output logic    [AXIRGN-1:0]  axi_mst_awregion,// write command

   output logic                  axi_mst_wvalid,  // write data valid
   input  logic                  axi_mst_wready,  // write data accept
   output logic    [AXIDW-1:0]   axi_mst_wdata,   // write data
   output logic    [AXIDW/8-1:0] axi_mst_wstrb,   // write data strobe
   output logic    [AXIWUW-1:0]  axi_mst_wuser,   // write data user field
   output logic                  axi_mst_wlast,   // write data last

   input  logic                  axi_mst_bvalid,  // write response valid
   output logic                  axi_mst_bready,  // write response accept
   input  logic    [AXIIDW-1:0]  axi_mst_bid,     // write response id
   input  logic    [AXIBUW-1:0]  axi_mst_buser,   // write response user field
   input  logic    [1:0]         axi_mst_bresp    // write response
   );

`ifdef AXI_WR_CMD_INJECT_STALL
  logic [2:0]         wcmd_stall_cntr; //up to 8  cycle
  always_ff @(posedge clk or posedge rst_a)
  begin : wcmd_stall_cntr_PROC
    if (rst_a ==1'b1)
    begin
      wcmd_stall_cntr  <= '0;
    end
    else
    begin
      if ((wcmd_stall_cntr == '0) && axi_mst_awready) begin
        wcmd_stall_cntr  <= $random;
      end
      else if (axi_slv_awvalid && (wcmd_stall_cntr != '0)) begin
        wcmd_stall_cntr  <= wcmd_stall_cntr - 'b1;
      end
    end
  end : wcmd_stall_cntr_PROC
`endif

`ifdef AXI_WR_DATA_INJECT_STALL
  logic [1:0]         wd_stall_cntr;   //up to 4  cycle
  always_ff @(posedge clk or posedge rst_a)
  begin : wd_stall_cntr_PROC
    if (rst_a ==1'b1)
    begin
      wd_stall_cntr    <= '0;
    end
    else
    begin
      if ((wd_stall_cntr == '0) && axi_mst_wready) begin
        wd_stall_cntr  <= $random;
      end
      else if (axi_slv_wvalid  && (wd_stall_cntr != '0)) begin
        wd_stall_cntr  <= wd_stall_cntr - 'b1;
      end
    end
  end : wd_stall_cntr_PROC
`endif

`ifdef AXI_WBSP_INJECT_STALL
  logic [3:0]         b_stall_cntr;    //up to 16 cycle
  always_ff @(posedge clk or posedge rst_a)
  begin : b_stall_cntr_PROC
    if (rst_a ==1'b1)
    begin
      b_stall_cntr     <= '0;
    end
    else
    begin
      if ((b_stall_cntr == '0) && axi_slv_bready) begin
        b_stall_cntr  <= $random;
      end
      else if (axi_mst_bvalid  && (b_stall_cntr != '0)) begin
        b_stall_cntr  <= b_stall_cntr - 'b1;
      end
    end
  end : b_stall_cntr_PROC
`endif

`ifdef AXI_RD_CMD_INJECT_STALL
  logic [2:0]         rcmd_stall_cntr; //up to 8  cycle
  always_ff @(posedge clk or posedge rst_a)
  begin : rcmd_stall_cntr_PROC
    if (rst_a ==1'b1)
    begin
      rcmd_stall_cntr  <= '0;
    end
    else
    begin
      if ((rcmd_stall_cntr == '0) && axi_mst_arready) begin
        rcmd_stall_cntr  <= $random;
      end
      else if (axi_slv_arvalid && (rcmd_stall_cntr != '0)) begin
        rcmd_stall_cntr  <= rcmd_stall_cntr - 'b1;
      end
    end
  end : rcmd_stall_cntr_PROC
`endif

`ifdef AXI_RD_DATA_INJECT_STALL
  logic [1:0]         rd_stall_cntr;   //up to 4  cycle
  always_ff @(posedge clk or posedge rst_a)
  begin : rd_stall_cntr_PROC
    if (rst_a ==1'b1)
    begin
      rd_stall_cntr    <= '0;
    end
    else
    begin
      if ((rd_stall_cntr == '0) && axi_slv_rready) begin
        rd_stall_cntr  <= $random;
      end
      else if (axi_mst_rvalid  && (rd_stall_cntr != '0)) begin
        rd_stall_cntr  <= rd_stall_cntr - 'b1;
      end
    end
  end : rd_stall_cntr_PROC
`endif

  // Assign output
  // Write Master
`ifdef AXI_WR_CMD_INJECT_STALL
  assign   axi_mst_awvalid      =  (wcmd_stall_cntr == '0) ? axi_slv_awvalid : '0;
  assign   axi_slv_awready      =  (wcmd_stall_cntr == '0) ? axi_mst_awready : '0;
`else
  assign   axi_mst_awvalid      =  axi_slv_awvalid ;
  assign   axi_slv_awready      =  axi_mst_awready ;
`endif

  assign   axi_mst_awid         =  axi_slv_awid    ;
  assign   axi_mst_awuser       =  axi_slv_awuser  ;
  assign   axi_mst_awaddr       =  axi_slv_awaddr  ;
  assign   axi_mst_awcache      =  axi_slv_awcache ;
  assign   axi_mst_awprot       =  axi_slv_awprot  ;
  assign   axi_mst_awlock       =  axi_slv_awlock  ;
  assign   axi_mst_awburst      =  axi_slv_awburst ;
  assign   axi_mst_awlen        =  axi_slv_awlen   ;
  assign   axi_mst_awsize       =  axi_slv_awsize  ;
  assign   axi_mst_awregion     =  axi_slv_awregion;

`ifdef AXI_WR_DATA_INJECT_STALL
  assign   axi_mst_wvalid       =  (wd_stall_cntr == '0) ? axi_slv_wvalid : '0;
  assign   axi_slv_wready       =  (wd_stall_cntr == '0) ? axi_mst_wready : '0;
`else
  assign   axi_mst_wvalid       =  axi_slv_wvalid  ;
  assign   axi_slv_wready       =  axi_mst_wready  ;
`endif

  assign   axi_mst_wdata        =  axi_slv_wdata   ;
  assign   axi_mst_wstrb        =  axi_slv_wstrb   ;
  assign   axi_mst_wuser        =  axi_slv_wuser   ;
  assign   axi_mst_wlast        =  axi_slv_wlast   ;

`ifdef AXI_WBSP_INJECT_STALL
  assign   axi_mst_bready       =  (b_stall_cntr == '0) ? axi_slv_bready : '0;
  assign   axi_slv_bvalid       =  (b_stall_cntr == '0) ? axi_mst_bvalid : '0;
`else
  assign   axi_mst_bready       =  axi_slv_bready  ;
  assign   axi_slv_bvalid       =  axi_mst_bvalid  ;
`endif

  assign   axi_slv_bid          =  axi_mst_bid     ;
  assign   axi_slv_buser        =  axi_mst_buser   ;
  assign   axi_slv_bresp        =  axi_mst_bresp   ;

  // Write Slave 

  // Read Master
`ifdef AXI_RD_CMD_INJECT_STALL
  assign   axi_mst_arvalid      =  (rcmd_stall_cntr == '0) ? axi_slv_arvalid : '0;
  assign   axi_slv_arready      =  (rcmd_stall_cntr == '0) ? axi_mst_arready : '0;
`else
  assign   axi_mst_arvalid      =  axi_slv_arvalid ;
  assign   axi_slv_arready      =  axi_mst_arready ;
`endif

  assign   axi_mst_arid         =  axi_slv_arid    ;
  assign   axi_mst_aruser       =  axi_slv_aruser  ;
  assign   axi_mst_araddr       =  axi_slv_araddr  ;
  assign   axi_mst_arcache      =  axi_slv_arcache ;
  assign   axi_mst_arprot       =  axi_slv_arprot  ;
  assign   axi_mst_arlock       =  axi_slv_arlock  ;
  assign   axi_mst_arburst      =  axi_slv_arburst ;
  assign   axi_mst_arlen        =  axi_slv_arlen   ;
  assign   axi_mst_arsize       =  axi_slv_arsize  ;
  assign   axi_mst_arregion     =  axi_slv_arregion;

  // Read Slave
`ifdef AXI_RD_DATA_INJECT_STALL
  assign   axi_slv_rvalid       =  (rd_stall_cntr == '0) ? axi_mst_rvalid : '0;
  assign   axi_mst_rready       =  (rd_stall_cntr == '0) ? axi_slv_rready : '0;
`else
  assign   axi_slv_rvalid       =  axi_mst_rvalid  ;
  assign   axi_mst_rready       =  axi_slv_rready  ;
`endif

  assign   axi_slv_rid          =  axi_mst_rid     ;
  assign   axi_slv_rdata        =  axi_mst_rdata   ;
  assign   axi_slv_rresp        =  axi_mst_rresp   ;
  assign   axi_slv_ruser        =  axi_mst_ruser   ;
  assign   axi_slv_rlast        =  axi_mst_rlast   ;

endmodule : npu_axi_inj_stall
