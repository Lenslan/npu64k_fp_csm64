/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictl:y prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

// Initiator part of AXI sync bridge

`include "npu_macros.svh"

`include "npu_defines.v"
`include "npu_axi_macros.svh"
  
module npu_axi_sync_ini
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
   // clock and reset and link power-down
   input  logic axi_slv_clk,
   input  logic axi_slv_rst_a,
   input  logic tgt_pwr_dwn_a,
   input  logic test_mode,
   // AXI slave interface
   `AXISLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master sync interface
   `AXISYNCMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,AWFIFO_DEPTHL2,WFIFO_DEPTHL2,BFIFO_DEPTHL2,ARFIFO_DEPTHL2,RFIFO_DEPTHL2,axi_sync_mst_)
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
  // reset, power down, clock request
  logic                            axi_slv_rst; 
  logic                            pwr_dwn;
  logic                            clk_req_r;
  logic                            clk_req_nxt;
  logic                            flush;
  // internal handshakes
  logic                            awv;
  logic                            awr;
  logic                            wv;
  logic                            wr;
  logic                            bv;
  logic                            br;
  logic                            arv;
  logic                            arr;
  logic                            rv;
  logic                            rr;
  // track pending read and write transactions, max 32 pending
  state_t                          state_r;
  state_t                          state_nxt;
  logic                            state_en;
  logic         [5:0]              wpend_r;
  logic         [5:0]              w2bpend_r;
  logic         [31:0]             b_val_r;
  logic         [31:0][AXIIDW-1:0] b_id_r;
  logic         [31:0]             r_val_r;
  logic         [31:0][AXIIDW-1:0] r_id_r;
  npu_axi_len_t [31:0]             r_len_r;
  logic         [5:0]              wpend_nxt;
  logic         [5:0]              w2bpend_nxt;
  logic         [31:0]             b_val_nxt;
  logic         [31:0][AXIIDW-1:0] b_id_nxt;
  logic         [31:0]             r_val_nxt;
  logic         [31:0][AXIIDW-1:0] r_id_nxt;
  npu_axi_len_t [31:0]             r_len_nxt;
  logic                            wpend_en;
  logic                            w2bpend_en;
  logic         [31:0]             b_en;
  logic         [31:0]             r_en;
  logic                            rstall;
  logic                            wstall;
  logic                            pwr_dwn_flush;

  // stall at 32 pending transactions or during reset
  assign axi_sync_mst_clk_req  = clk_req_r;
  assign clk_req_nxt           = {r_val_nxt, b_val_nxt, wpend_nxt} != '0;
  assign flush                 = (state_r == state_flush_e) | (state_r == state_pwr_dwn_e);
  assign rstall                = (r_val_r[31] & r_val_r[0]) | (state_r == state_reset_e) | (state_r == state_flush_e);
  assign wstall                = wpend_r[5] | (b_val_r[31] & b_val_r[0]) | (state_r == state_reset_e) | (state_r == state_flush_e);
  assign arv                   = axi_slv_arvalid & (~rstall);
  assign axi_slv_arready       = (arr | (state_r == state_pwr_dwn_e)) & (~rstall);
  assign awv                   = axi_slv_awvalid & (~wstall);
  assign axi_slv_awready       = (awr | (state_r == state_pwr_dwn_e)) & (~wstall);
  assign wv                    = (axi_slv_wvalid & (~flush)) & (wpend_r != '0);
  assign axi_slv_wready        = (wr | flush) & (wpend_r != '0);
  assign axi_slv_bvalid        = flush ? b_val_r[0] & (w2bpend_r != '0) : bv;
  assign br                    = flush ? 1'b0 : axi_slv_bready;
  assign axi_slv_rvalid        = flush ? r_val_r[0] : rv;
  assign rr                    = flush ? 1'b0 : axi_slv_rready;
  

  //  
  // Local reset synchronizer
  //
  npu_reset_ctrl 
  u_reset_ctrl_main
  (
   .clk        ( axi_slv_clk   ),
   .rst_a      ( axi_slv_rst_a ),
   .test_mode  ( test_mode     ),
   .rst        ( axi_slv_rst   )
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
  u_event_cdc_sync 
  (
   .clk        ( axi_slv_clk   ),
   .rst_a      ( axi_slv_rst   ),
   .din        ( {1{tgt_pwr_dwn_a}} ),
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
    pwr_dwn_flush = 1'b0;
    case (state_r)
    state_reset_e:
      begin
        state_en = 1'b1;
        if (pwr_dwn)
        begin
          // go to power-down state
          state_nxt = state_pwr_dwn_e;
        end
        else
        begin
          // go to active
          state_nxt = state_active_e;
        end
      end
    state_flush_e:
      begin
        if (pwr_dwn)
        begin
          // go to power-down state
          state_en  = 1'b1;
          state_nxt = state_pwr_dwn_e;
        end
        else if (!clk_req_nxt)
        begin
          // all flushed, go to active
          state_en  = 1'b1;
          state_nxt = state_active_e;
        end
      end
    state_pwr_dwn_e:
      begin
        if (!pwr_dwn)
        begin
          state_en = 1'b1;
          state_nxt = state_flush_e;
          pwr_dwn_flush = 1'b1;
        end
      end
    default: // state_active_e
      begin
        if (pwr_dwn)
        begin
          state_en = 1'b1;
          state_nxt = state_pwr_dwn_e;
        end
      end
    endcase
  end : state_nxt_PROC
  
  
  //
  // Track read data
  //
  always_comb
  begin : rtrack_PROC
    logic f;
    // default outputs
    r_val_nxt = r_val_r;
    r_id_nxt  = r_id_r;
    r_len_nxt = r_len_r;
    r_en      = '0;
    // rotate buffer
    if (((r_val_r[31]) & (~r_val_r[0])) || (flush & (~r_val_r[0])))
    begin
      for (int i = 0; i < 31; i++)
      begin
        r_val_nxt[i] = r_val_nxt[i+1];
        r_id_nxt[i]  = r_id_nxt[i+1];
        r_len_nxt[i] = r_len_nxt[i+1];
      end
      r_val_nxt[31] = 1'b0;
      r_en = '1;
    end
    // remove data
    f = 1'b1;
    if (axi_slv_rvalid & axi_slv_rready)
    begin
      for (int i = 0; i < 32; i++)
      begin
        if (f && r_val_nxt[i] && (r_id_nxt[i] == axi_slv_rid))
        begin
          r_val_nxt[i] = !axi_slv_rlast;
          r_len_nxt[i] = r_len_nxt[i] - 'd1;
          r_en[i]      = 1'b1;
          f            = 1'b0;
        end
      end
    end
    // add command
    if (axi_slv_arvalid & axi_slv_arready)
    begin
      r_val_nxt[31] = 1'b1;
      r_id_nxt[31]  = axi_slv_arid;
      r_len_nxt[31] = axi_slv_ar.len;
      r_en[31]      = 1'b1;
    end
  end : rtrack_PROC

  
  //
  // Track write data
  //
  always_comb
  begin : track_nxt_PROC
    // default outputs
    wpend_en     = 1'b0;
    wpend_nxt    = wpend_r;
    // increment counter on new command
    if (axi_slv_awvalid & axi_slv_awready)
    begin
      wpend_en   = 1'b1;
      wpend_nxt  = wpend_nxt + 'd1;
    end
    // decrement counters on last
    if (axi_slv_wvalid & axi_slv_wready & axi_slv_wlast)
    begin
      wpend_en   = 1'b1;
      wpend_nxt  = wpend_nxt - 'd1;
    end
  end : track_nxt_PROC

  //
  // Track write counter between W and B channel
  //
  always_comb
  begin : track_W2B_nxt_PROC
    // default outputs
    w2bpend_en     = 1'b0;
    w2bpend_nxt    = w2bpend_r;
    // decrement counter on new command
    if (axi_slv_bvalid & axi_slv_bready)
    begin
      w2bpend_en   = 1'b1;
      w2bpend_nxt  = w2bpend_nxt - 'd1;
    end
    // increment counters on wlast
    if (axi_slv_wvalid & axi_slv_wready & axi_slv_wlast)
    begin
      w2bpend_en   = 1'b1;
      w2bpend_nxt  = w2bpend_nxt + 'd1;
    end
  end : track_W2B_nxt_PROC
  
  //
  // Track write response
  //
  always_comb
  begin : btrack_PROC
    logic f;
    // default outputs
    b_val_nxt = b_val_r;
    b_id_nxt  = b_id_r;
    b_en      = '0;
    // rotate buffer
    if (((b_val_r[31]) & (~b_val_r[0])) || (flush & (~b_val_r[0])))
    begin
      for (int i = 0; i < 31; i++)
      begin
        b_val_nxt[i] = b_val_nxt[i+1];
        b_id_nxt[i]  = b_id_nxt[i+1];
      end
      b_val_nxt[31] = 1'b0;
      b_en = '1;
    end
    // remove data
    f = 1'b1;
    if (axi_slv_bvalid & axi_slv_bready)
    begin
      for (int i = 0; i < 32; i++)
      begin
        if (f && b_val_nxt[i] && (b_id_nxt[i] == axi_slv_bid))
        begin
          b_val_nxt[i] = 1'b0;
          b_en[i]      = 1'b1;
          f            = 1'b0;
        end
      end
    end
    // add command
    if (axi_slv_awvalid & axi_slv_awready)
    begin
      b_val_nxt[31] = 1'b1;
      b_id_nxt[31]  = axi_slv_awid;
      b_en[31]      = 1'b1;
    end
  end : btrack_PROC


  //
  // State for pending transactions and clock request
  //
  always_ff @(posedge axi_slv_clk or posedge axi_slv_rst)
  begin : track_reg_PROC
    if (axi_slv_rst == 1'b1)
    begin
      state_r   <= state_reset_e;
      clk_req_r <= 1'b1;
      r_val_r   <= '0;
      r_id_r    <= '0;
      r_len_r   <= '0;
      wpend_r   <= '0;
      w2bpend_r <= '0;
      b_val_r   <= '0;
      b_id_r    <= '0;
    end
    else
    begin
      if (state_en)
      begin
        state_r <= state_nxt;
      end
      clk_req_r <= clk_req_nxt;
      for (int i = 0; i < 32; i++)
      begin
        if (r_en[i])
        begin
          r_val_r[i] <= r_val_nxt[i];
          r_id_r[i]  <= r_id_nxt[i];
          r_len_r[i] <= r_len_nxt[i];
        end
      end
      if (wpend_en)
      begin
        wpend_r <= wpend_nxt;
      end
      if (w2bpend_en)
      begin
        w2bpend_r <= w2bpend_nxt;
      end
      for (int i = 0; i < 32; i++)
      begin
        if (b_en[i])
        begin
          b_val_r[i] <= b_val_nxt[i];
          b_id_r[i]  <= b_id_nxt[i];
        end
      end
    end
  end : track_reg_PROC


  //
  // Write command FIFO
  //
  aw_t axi_slv_awtmp;
  assign axi_slv_awtmp.awid   = axi_slv_awid;
  assign axi_slv_awtmp.awuser = axi_slv_awuser;
  assign axi_slv_awtmp.aw     = axi_slv_aw;
  npu_fifo_w
  #(
    .FIFO_SIZEL2     ( AWFIFO_DEPTHL2         ),
    .FIFO_DATA_WIDTH ( $bits(aw_t)            )
  )
  aw_fifo_inst
  (
   .write_clk      ( axi_slv_clk               ),
   .write_rst      ( axi_slv_rst               ),
   .write_soft_rst ( pwr_dwn_flush             ),
   .write_valid    ( awv                       ),
   .write_accept   ( awr                       ),
   .write_data     ( axi_slv_awtmp             ),
   .rdpnt          ( axi_sync_mst_aw_rdpnt     ),
   .rdata          ( axi_sync_mst_aw_data      ),
   .wpnt           ( axi_sync_mst_aw_wpnt      ),
   .rpnt           ( axi_sync_mst_aw_rpnt      )
  );


  //
  // Write data FIFO
  //
  w_t axi_slv_wtmp;
  assign axi_slv_wtmp.wdata = axi_slv_wdata;
  assign axi_slv_wtmp.wstrb = axi_slv_wstrb;
  assign axi_slv_wtmp.wuser = axi_slv_wuser;
  assign axi_slv_wtmp.wlast = axi_slv_wlast;
  npu_fifo_w
  #(
    .FIFO_SIZEL2     ( WFIFO_DEPTHL2       ),
    .FIFO_DATA_WIDTH ( $bits(w_t)          )
  )
  w_fifo_inst
  (
   .write_clk      ( axi_slv_clk              ),
   .write_rst      ( axi_slv_rst              ),
   .write_soft_rst ( pwr_dwn_flush            ),
   .write_valid    ( wv                       ),
   .write_accept   ( wr                       ),
   .write_data     ( axi_slv_wtmp             ),
   .rdpnt          ( axi_sync_mst_w_rdpnt     ),
   .rdata          ( axi_sync_mst_w_data      ),
   .wpnt           ( axi_sync_mst_w_wpnt      ),
   .rpnt           ( axi_sync_mst_w_rpnt      )
  );
  

  //
  // Write response FIFO
  //
  b_t axi_slv_btmp;
  assign axi_slv_bid        = flush ? b_id_r[0] : axi_slv_btmp.bid;
  assign axi_slv_buser      = flush ? '0 : axi_slv_btmp.buser;
  assign axi_slv_bresp      = flush ? npu_axi_resp_slverr_e : axi_slv_btmp.bresp;
  npu_fifo_r
  #(
    .FIFO_SIZEL2     ( BFIFO_DEPTHL2        ),
    .FIFO_DATA_WIDTH ( $bits(b_t)           )
  )
  b_fifo_inst
  (
   .read_clk      ( axi_slv_clk              ),
   .read_rst      ( axi_slv_rst              ),
   .read_soft_rst ( pwr_dwn_flush            ),
   .read_valid    ( bv                       ),
   .read_accept   ( br                       ),
   .read_data     ( axi_slv_btmp             ),
   .rdpnt         ( axi_sync_mst_b_rdpnt     ),
   .rdata         ( axi_sync_mst_b_data      ),
   .wpnt          ( axi_sync_mst_b_wpnt      ),
   .rpnt          ( axi_sync_mst_b_rpnt      )
  );
  

  //
  // Read command FIFO
  //
  ar_t axi_slv_artmp;
  assign axi_slv_artmp.arid   = axi_slv_arid;
  assign axi_slv_artmp.aruser = axi_slv_aruser;
  assign axi_slv_artmp.ar     = axi_slv_ar;
  npu_fifo_w
  #(
    .FIFO_SIZEL2     ( ARFIFO_DEPTHL2         ),
    .FIFO_DATA_WIDTH ( $bits(ar_t)            )
  )
  ar_fifo_inst
  (
   .write_clk      ( axi_slv_clk               ),
   .write_rst      ( axi_slv_rst               ),
   .write_soft_rst ( pwr_dwn_flush             ),
   .write_valid    ( arv                       ),
   .write_accept   ( arr                       ),
   .write_data     ( axi_slv_artmp             ),
   .rdpnt          ( axi_sync_mst_ar_rdpnt     ),
   .rdata          ( axi_sync_mst_ar_data      ),
   .wpnt           ( axi_sync_mst_ar_wpnt      ),
   .rpnt           ( axi_sync_mst_ar_rpnt      )
  );

  
  //
  // Read data FIFO
  //
  r_t axi_slv_rtmp;
  assign axi_slv_rid        = flush ? r_id_r[0] : axi_slv_rtmp.rid;
  assign axi_slv_rdata      = axi_slv_rtmp.rdata;
  assign axi_slv_rresp      = flush ? npu_axi_resp_slverr_e : axi_slv_rtmp.rresp;
  assign axi_slv_ruser      = flush ? '0 : axi_slv_rtmp.ruser;
  assign axi_slv_rlast      = flush ? r_len_r[0] == '0 : axi_slv_rtmp.rlast;
  npu_fifo_r
  #(
    .FIFO_SIZEL2     ( RFIFO_DEPTHL2         ),
    .FIFO_DATA_WIDTH ( $bits(r_t)            )
  )
  r_fifo_inst
  (
   .read_clk      ( axi_slv_clk              ),
   .read_rst      ( axi_slv_rst              ),
   .read_soft_rst ( pwr_dwn_flush            ),
   .read_valid    ( rv                       ),
   .read_accept   ( rr                       ),
   .read_data     ( axi_slv_rtmp             ),
   .rdpnt         ( axi_sync_mst_r_rdpnt     ),
   .rdata         ( axi_sync_mst_r_data      ),
   .wpnt          ( axi_sync_mst_r_wpnt      ),
   .rpnt          ( axi_sync_mst_r_rpnt      )
  );


endmodule : npu_axi_sync_ini
