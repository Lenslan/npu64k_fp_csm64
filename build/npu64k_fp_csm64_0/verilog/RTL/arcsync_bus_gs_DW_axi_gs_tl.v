// ---------------------------------------------------------------------
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
// File Version     :        $Revision: #7 $
// Revision: $Id: //dwh/DW_ocb/DW_axi_gs/amba_dev/src/DW_axi_gs_tl.v#7 $
//
// ---------------------------------------------------------------------
//
// AUTHOR:    Jorge Duarte      6/17/2010
//
// VERSION:   DW_axi_gs_tl Verilog Synthesis Model
//
//
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
//
// ABSTRACT:  Transaction counter
//
// The spec for low power operation calls for the device to remain
// powered up while there are pending transactions. This block keeps
// track of pending read and write transactions and informs the low
// power state machine of whether or not there are any pending
// transactions.
//
// The beginning of a write transaction is detected by sampling awvalid
// and awready high simultaneoulsy; the beginning of a read transaction
// is detected by sampling arvalid and arready high simultaneously.
// The pending transactions counter is incremented whenever either of
// these situations occurs.
//
// The completion of a write transaction is detected by sampling bvalid
// and bready high simultaneously; the completion of a read transaction
// is detected by sampling rvalid, rlast and rready simultaneously. The
// pending transactions counter is decremented whenever either of these
// situations occurs.
//
// It is possible for transactions to be initiated and completed in the
// same clock cycle. The component arbitrates between read and write
// requests so it is not possible for read and write transactions to be
// initiated simultaneously; it is also not possible for read and write
// transaction to complete simultaneously. However it is possible for a
// write or read transaction to complete at the same time a new read
// or transaction is initiated; the following scenarios are handled
// correctly by the counter:
//   1.no transaction completed or initiated: counter value remains the
//     same
//   2.one transaction (read or write) is completed; no transaction is
//     initiated; counter value is decremented by 1
//   3.one transaction (read or write) is initiated; no transaction is
//     completed; counter value is incremented by 1
//   4.one transaction (read or write) is completed; one transaction
//     (read or write) is initiated; counter value remains the same
//
// Because it is only necessary to know whether there are any pending
// transactions and no information is required about the status of each
// individual transaction, the active_trans output is generated by
// evaluating the value of the pending transactions counter; if its
// value is different from 0, active_trans will be high.
// awvalid and arvalid are also used to generate active_trans; this is
// done in order to support the combinational assertion of cactive by
// these signals (awvalid and arvalid) when in low power mode (clock
// disabled).
//
// ---------------------------------------------------------------------

`include "arcsync_bus_gs_DW_axi_gs_all_includes.vh"

module arcsync_bus_gs_DW_axi_gs_tl(
  // Outputs
  active_trans,
  // Inputs
  aclk, aresetn, gclken,
  awvalid, awready,
  bvalid, bready,
  arvalid, arready,
  rvalid, rlast, rready
  );

output active_trans;

// AXI INTERFACE
// Global
input  aclk;
input  aresetn;
input  gclken;
// Write address channel
input  awvalid;
input  awready;
// Write response channel
input  bvalid;
input  bready;
// Read address channel
input  arvalid;
input  arready;
// Read data channel
input  rlast;
input  rvalid;
input  rready;

reg  [`ARCSYNC_REG_GS_LOWPWR_PENDTRANS_CNT_W:0] pend_trans_cnt;
wire [`ARCSYNC_REG_GS_LOWPWR_PENDTRANS_CNT_W:0] pend_trans_cnt_c;

wire       init_write_trans;
wire       init_read_trans;
wire       compl_write_trans;
wire       compl_read_trans;

wire       active_trans;

assign init_write_trans  = awvalid && awready && gclken;
assign init_read_trans   = arvalid && arready && gclken;
assign compl_write_trans = bvalid && bready;
assign compl_read_trans  = rvalid && rlast && rready;

// Counter for pending write transactions
assign pend_trans_cnt_c = pend_trans_cnt;
always@(posedge aclk or negedge aresetn)
begin: PEND_TRANS_CNT_PROC
  if ( !aresetn )
    pend_trans_cnt <= {(`ARCSYNC_REG_GS_LOWPWR_PENDTRANS_CNT_W+1){1'b0}};
  else
  begin
    case ( { ( compl_write_trans || compl_read_trans ),
             ( init_write_trans  || init_read_trans  ) } )
      2'b00 : pend_trans_cnt <= pend_trans_cnt_c;
      2'b01 : pend_trans_cnt <= pend_trans_cnt_c + 1;
      2'b10 : pend_trans_cnt <= pend_trans_cnt_c - 1;
      2'b11 : pend_trans_cnt <= pend_trans_cnt_c;
    endcase
  end
end

assign active_trans = ( pend_trans_cnt > 0 ) || awvalid || arvalid ;

endmodule
