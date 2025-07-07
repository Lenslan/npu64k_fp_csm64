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

// Target part of AXI sync bridge

`include "npu_macros.svh"

`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_axi_sync_tgt
  import npu_types::*;
  #(
    parameter int AXIIDW         = 4,
    parameter int AXIDW          = 128,
    parameter int AXIAWUW        = 1,
    parameter int AXIWUW         = 1,
    parameter int AXIBUW         = 1,
    parameter int AXIARUW        = 1,
    parameter int AXIRUW         = 1,
    // FIFO depth specification
    parameter int AWFIFO_DEPTHL2 = 0,
    parameter int WFIFO_DEPTHL2  = 1,
    parameter int BFIFO_DEPTHL2  = 0,
    parameter int ARFIFO_DEPTHL2 = 0,
    parameter int RFIFO_DEPTHL2  = 1
  )
  (
   // clock and reset
   input  logic axi_mst_clk,
   input  logic axi_mst_rst_a,
   input  logic ini_pwr_dwn_a,
   input  logic test_mode,
   output logic clk_req,
   // AXI master interface
   `AXIMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
   // AXI slave sync interface
   `AXISYNCSLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWFIFO_DEPTHL2,WFIFO_DEPTHL2,BFIFO_DEPTHL2,ARFIFO_DEPTHL2,RFIFO_DEPTHL2,axi_sync_slv_)
   );
  // type definitions
  typedef struct packed {
    logic          [AXIIDW-1:0]  awid;
    logic          [AXIAWUW-1:0] awuser;
    npu_axi_cmd_t                aw;
  } aw_t;
  typedef struct packed {
    logic          [AXIDW-1:0]   wdata;
    logic          [AXIDW/8-1:0] wstrb;
    logic          [AXIWUW-1:0]  wuser;
    logic                        wlast;
  } w_t;
  typedef struct packed {
    logic          [AXIIDW-1:0]  bid;
    logic          [AXIBUW-1:0]  buser;
    npu_axi_resp_t               bresp;
  } b_t;
  typedef struct packed {
    logic          [AXIIDW-1:0]  arid;
    logic          [AXIARUW-1:0] aruser;
    npu_axi_cmd_t                ar;
  } ar_t;
  typedef struct packed {
    logic          [AXIIDW-1:0]  rid;
    logic          [AXIDW-1:0]   rdata;
    npu_axi_resp_t               rresp;
    logic          [AXIRUW-1:0]  ruser;
    logic                        rlast;
  } r_t;
  typedef enum logic [1:0] {
                            state_reset_e,    // after hard reset
                            state_active_e,   // active mode
                            state_pwr_dwn_e,  // target goes into power down, complete all pending and new transactions
                            state_flush_e     // flush all pending transactions, complete all pending transactions, stall new
                            } state_t;
  // reset, clock request, power down
  logic               axi_mst_rst;
  logic               pwr_dwn;
  logic               clk_req_r;         // forced clock request in non-active states
  logic               clk_req_nxt;
  // state
  state_t             state_r;
  state_t             state_nxt;
  logic               state_en;
  logic               arflush_r;         // unfinished read command
  logic               awflush_r;         // unfinished write command
  logic               wflush_r;          // unfinished write data
  logic               arflush_nxt;
  logic               awflush_nxt;
  logic               wflush_nxt;
  logic         [5:0] bpend_r;
  logic         [5:0] rpend_r;
  logic         [5:0] bpend_nxt;
  logic         [5:0] rpend_nxt;
  logic               bpend_en;
  logic               rpend_en;
  logic               wfifo_wvalid;     // controls for write data tracking FIFO
  logic               wfifo_waccept;
  logic               wfifo_rvalid;
  logic               wfifo_raccept;
  npu_axi_len_t       wfifo_rdata;
  npu_axi_len_t       wlen_r;
  npu_axi_len_t       wlen_nxt;
  logic               wlen_en;
  logic               idle;
  logic               flush;
  logic               pwr_dwn_flush;
  // internal handshakes
  logic               awv;
  logic               awr;
  logic               wv;
  logic               wr;
  logic               bv;
  logic               br;
  logic               arv;
  logic               arr;
  logic               rv;
  logic               rr;

  
  //
  // simple assignments
  //
  assign clk_req         = axi_sync_slv_clk_req | clk_req_r;
  assign idle            = {arflush_r, awflush_r, wflush_r, bpend_r, rpend_r, wfifo_rvalid} == '0;
  assign flush           = state_r == state_pwr_dwn_e || state_r == state_flush_e;
  assign axi_mst_awvalid = (flush ? awflush_r : awv) & wfifo_waccept;
  assign awr             = flush ? 1'b0 : axi_mst_awready & wfifo_waccept;
  assign axi_mst_wvalid  = flush ? wfifo_rvalid : wfifo_rvalid & wv;
  assign wr              = flush ? 1'b0 : wfifo_rvalid & axi_mst_wready;
  assign bv              = flush ? 1'b0 : axi_mst_bvalid;
  assign axi_mst_bready  = flush ? 1'b1 : br;
  assign axi_mst_arvalid = flush ? arflush_r : arv;
  assign arr             = flush ? 1'b0 : axi_mst_arready;
  assign rv              = flush ? 1'b0 : axi_mst_rvalid;
  assign axi_mst_rready  = flush ? 1'b1 : rr;
  
  //
  // local reset synchronizer
  //
  npu_reset_ctrl 
  u_reset_ctrl_main
  (
   .clk        ( axi_mst_clk   ),
   .rst_a      ( axi_mst_rst_a ),
   .test_mode  ( test_mode     ),
   .rst        ( axi_mst_rst   )
  );

  //
  // Synchronize power-down input
  //
  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS(2), 
    .WIDTH(1),
    .TMR_CDC(0)
  ) 
  u_ini_pwr_dwn_event_cdc_sync 
  (
   .clk        ( axi_mst_clk   ),
   .rst_a      ( axi_mst_rst   ),
   .din        ( {1{ini_pwr_dwn_a}} ),
   .dout       ( pwr_dwn       )
  );


  //
  // State machine
  //
  always_comb
  begin : state_nxt_PROC
    // defaults
    state_en      = 1'b0;
    state_nxt     = state_reset_e;
    arflush_nxt   = arflush_r;
    awflush_nxt   = awflush_r;
    wflush_nxt    = wflush_r;
    clk_req_nxt   = clk_req_r;
    pwr_dwn_flush = 1'b0;
    case (state_r)
    state_reset_e:
      begin
        state_en    = 1'b1;
        if (pwr_dwn)
        begin
          // go to power-down state
          state_nxt = state_pwr_dwn_e;
        end
        else
        begin
          // go to active
          state_nxt   = state_active_e;
          clk_req_nxt = 1'b0;
        end
      end
    state_flush_e:
      begin
        // continue pending commands

        if (pwr_dwn)
        begin
          state_en      = 1'b1;
          state_nxt     = state_pwr_dwn_e;
        end
        else if (idle)
        begin
          state_en    = 1'b1;
          state_nxt   = state_active_e;
          clk_req_nxt = 1'b0;
        end
      end
    state_pwr_dwn_e:
      begin
        // continue pending commands
        arflush_nxt &= ~axi_mst_arready;
        awflush_nxt &= ~(axi_mst_awready&wfifo_waccept);
        wflush_nxt  &= ~axi_mst_wready;
        if (!pwr_dwn)
        begin
          // reset FIFOs
          state_en      = 1'b1;
          state_nxt     = state_flush_e;
          pwr_dwn_flush = 1'b1;
          arflush_nxt  &= 1'b0;
          awflush_nxt  &= 1'b0;
          wflush_nxt   &= 1'b0;
        end
      end
    default: // state_active_e
      begin
        if (pwr_dwn)
        begin
          clk_req_nxt = 1'b1;
          state_en    = 1'b1;
          state_nxt   = state_pwr_dwn_e;
          arflush_nxt = axi_mst_arvalid & (~axi_mst_arready);
          awflush_nxt = axi_mst_awvalid & (~axi_mst_awready);
          wflush_nxt  = axi_mst_wvalid & (~axi_mst_wready);
        end
      end
    endcase // case (state_r)
  end : state_nxt_PROC
  

  //
  // Track pending write data
  //
  assign wfifo_wvalid  = axi_mst_awvalid & axi_mst_awready;
  assign wfifo_raccept = axi_mst_wvalid & axi_mst_wready & axi_mst_wlast;
  npu_fifo
  #(
    .SIZE   ( 32            ),
    .DWIDTH ( NPU_AXI_LEN_W )
  )
  u_wtrack_inst
  (
   .clk          ( axi_mst_clk    ),
   .rst_a        ( axi_mst_rst    ),
   .valid_write  ( wfifo_wvalid   ),
   .accept_write ( wfifo_waccept  ),
   .data_write   ( axi_mst_aw.len ),
   .valid_read   ( wfifo_rvalid   ),
   .accept_read  ( wfifo_raccept  ),
   .data_read    ( wfifo_rdata    )
  );
  assign wlen_en        = axi_mst_wvalid & axi_mst_wready;
  assign wlen_nxt       = wlen_r == 0 ? wfifo_rdata : wlen_r - 'd1;
  assign axi_mst_wlast  = wlen_nxt == '0;


  //
  // Track pending write responses
  //
  always_comb
  begin : btrack_PROC
    // defaults
    bpend_en = 1'b0;
    bpend_nxt = bpend_r;
    if (axi_mst_awvalid & axi_mst_awready)
    begin
      bpend_en = 1'b1;
      bpend_nxt = bpend_nxt + 'd1;
    end
    if (axi_mst_bvalid & axi_mst_bready)
    begin
      bpend_en = 1'b1;
      bpend_nxt = bpend_nxt - 'd1;
    end
  end : btrack_PROC
  

  //
  // Track pending read responses
  //
  always_comb
  begin : rtrack_PROC
    // defaults
    rpend_en = 1'b0;
    rpend_nxt = rpend_r;
    if (axi_mst_arvalid & axi_mst_arready)
    begin
      // add new command
      rpend_en  = 1'b1;
      rpend_nxt = rpend_nxt + 'd1;
    end
    if (axi_mst_rvalid & axi_mst_rready & axi_mst_rlast)
    begin
      // subtract finished command
      rpend_en  = 1'b1;
      rpend_nxt = rpend_nxt - 'd1;
    end
  end : rtrack_PROC
  

  //
  // State registers
  //
  //
  always_ff @(posedge axi_mst_clk or posedge axi_mst_rst)
  begin : state_reg_PROC
    if (axi_mst_rst == 1'b1)
    begin
      state_r   <= state_reset_e;
      clk_req_r <= 1'b1;
      wlen_r    <= '0;
      rpend_r   <= '0;
      bpend_r   <= '0;
      arflush_r <= 1'b0;
      awflush_r <= 1'b0;
      wflush_r  <= 1'b0;
    end
    else
    begin
      if (state_en)
      begin
        state_r <= state_nxt;
      end
      clk_req_r <= clk_req_nxt;
      if (wlen_en)
      begin
        wlen_r <= wlen_nxt;
      end
      if (rpend_en)
      begin
        rpend_r <= rpend_nxt;
      end
      if (bpend_en)
      begin
        bpend_r <= bpend_nxt;
      end
      arflush_r <= arflush_nxt;
      awflush_r <= awflush_nxt;
      wflush_r  <= wflush_nxt;
    end
  end : state_reg_PROC
  //

  
  

  //
  // FIFOs
  //


  //
  // Write command FIFO
  //
  aw_t axi_mst_awtmp;
  assign axi_mst_awid         = axi_mst_awtmp.awid;
  assign axi_mst_awuser       = axi_mst_awtmp.awuser;
  assign axi_mst_aw           = axi_mst_awtmp.aw;
  npu_fifo_r
  #(
    .FIFO_SIZEL2     ( AWFIFO_DEPTHL2         ),
    .FIFO_DATA_WIDTH ( $bits(aw_t)            )
  )
  aw_fifo_inst
  (
   .read_clk      ( axi_mst_clk               ),
   .read_rst      ( axi_mst_rst               ),
   .read_soft_rst ( pwr_dwn_flush             ),
   .read_valid    ( awv                       ),
   .read_accept   ( awr                       ),
   .read_data     ( axi_mst_awtmp             ),
   .rdpnt         ( axi_sync_slv_aw_rdpnt     ),
   .rdata         ( axi_sync_slv_aw_data      ),
   .wpnt          ( axi_sync_slv_aw_wpnt      ),
   .rpnt          ( axi_sync_slv_aw_rpnt      )
  );


  //
  // Write data FIFO
  //
  w_t axi_mst_wtmp;
  assign axi_mst_wdata      = flush & (~wflush_r) ? '0 : axi_mst_wtmp.wdata;
  assign axi_mst_wstrb      = flush & (~wflush_r) ? '0 : axi_mst_wtmp.wstrb;
  assign axi_mst_wuser      = flush & (~wflush_r) ? '0 : axi_mst_wtmp.wuser;
  npu_fifo_r
  #(
    .FIFO_SIZEL2     ( WFIFO_DEPTHL2       ),
    .FIFO_DATA_WIDTH ( $bits(w_t)          )
  )
  w_fifo_inst
  (
   .read_clk      ( axi_mst_clk              ),
   .read_rst      ( axi_mst_rst              ),
   .read_soft_rst ( pwr_dwn_flush            ),
   .read_valid    ( wv                       ),
   .read_accept   ( wr                       ),
   .read_data     ( axi_mst_wtmp             ),
   .rdpnt         ( axi_sync_slv_w_rdpnt     ),
   .rdata         ( axi_sync_slv_w_data      ),
   .wpnt          ( axi_sync_slv_w_wpnt      ),
   .rpnt          ( axi_sync_slv_w_rpnt      )
  );
  

  //
  // Write response FIFO
  //
  b_t axi_mst_btmp;
  assign axi_mst_btmp.bid   = axi_mst_bid;
  assign axi_mst_btmp.buser = axi_mst_buser;
  assign axi_mst_btmp.bresp = axi_mst_bresp;
  npu_fifo_w
  #(
    .FIFO_SIZEL2     ( BFIFO_DEPTHL2       ),
    .FIFO_DATA_WIDTH ( $bits(b_t)          )
  )
  b_fifo_inst
  (
   .write_clk      ( axi_mst_clk              ),
   .write_rst      ( axi_mst_rst              ),
   .write_soft_rst ( pwr_dwn_flush            ),
   .write_valid    ( bv                       ),
   .write_accept   ( br                       ),
   .write_data     ( axi_mst_btmp             ),
   .rdpnt          ( axi_sync_slv_b_rdpnt     ),
   .rdata          ( axi_sync_slv_b_data      ),
   .wpnt           ( axi_sync_slv_b_wpnt      ),
   .rpnt           ( axi_sync_slv_b_rpnt      )
  );
  

  //
  // Read command FIFO
  //
  ar_t axi_mst_artmp;
  assign axi_mst_arid         = axi_mst_artmp.arid;
  assign axi_mst_aruser       = axi_mst_artmp.aruser;
  assign axi_mst_ar           = axi_mst_artmp.ar;
  npu_fifo_r
  #(
    .FIFO_SIZEL2     ( ARFIFO_DEPTHL2         ),
    .FIFO_DATA_WIDTH ( $bits(ar_t)            )
  )
  ar_fifo_inst
  (
   .read_clk      ( axi_mst_clk               ),
   .read_rst      ( axi_mst_rst               ),
   .read_soft_rst ( pwr_dwn_flush             ),
   .read_valid    ( arv                       ),
   .read_accept   ( arr                       ),
   .read_data     ( axi_mst_artmp             ),
   .rdpnt         ( axi_sync_slv_ar_rdpnt     ),
   .rdata         ( axi_sync_slv_ar_data      ),
   .wpnt          ( axi_sync_slv_ar_wpnt      ),
   .rpnt          ( axi_sync_slv_ar_rpnt      )
  );

  
  //
  // Read data FIFO
  //
  r_t axi_mst_rtmp;
  assign axi_mst_rtmp.rid   = axi_mst_rid;
  assign axi_mst_rtmp.rdata = axi_mst_rdata;
  assign axi_mst_rtmp.rresp = axi_mst_rresp;
  assign axi_mst_rtmp.ruser = axi_mst_ruser;
  assign axi_mst_rtmp.rlast = axi_mst_rlast;
  npu_fifo_w
  #(
    .FIFO_SIZEL2     ( RFIFO_DEPTHL2         ),
    .FIFO_DATA_WIDTH ( $bits(r_t)            )
  )
  r_fifo_inst
  (
   .write_clk      ( axi_mst_clk              ),
   .write_rst      ( axi_mst_rst              ),
   .write_soft_rst ( pwr_dwn_flush            ),
   .write_valid    ( rv                       ),
   .write_accept   ( rr                       ),
   .write_data     ( axi_mst_rtmp             ),
   .rdpnt          ( axi_sync_slv_r_rdpnt     ),
   .rdata          ( axi_sync_slv_r_data      ),
   .wpnt           ( axi_sync_slv_r_wpnt      ),
   .rpnt           ( axi_sync_slv_r_rpnt      )
  );

endmodule : npu_axi_sync_tgt
