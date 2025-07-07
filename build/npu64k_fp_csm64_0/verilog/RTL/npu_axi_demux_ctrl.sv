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

// Route AXI transactions based on address bits
// The address map is passed as a set of signals
// If apertures overlap then the first will win
// e.g. decbase[3]=20'hf0000, decsize[3]=20'hffff0, decmst[3]='d4
// means aperture 3 from 0xf0000000 to 0xf000ffff will map to master port log2(4)=2
// if apertures overlap then last will win, so if a default aperture is required define it
// so for a default port set decbase[0] = 0, decsize[0] = ffffffff, dec


`include "npu_axi_macros.svh"

module npu_axi_demux_ctrl
  import npu_types::*;
  #(
    parameter int  NUMMST  = 2,            // number of master ports (one slave)
    parameter int  NUMAP   = 1,            // number of address apertures in address decoder
    parameter int  NUMID   = 16,           // maximum number of pending IDs per read and write
    parameter int  AXIDW   = 32,           // data width
    parameter int  AXIIDW  = 4,            // AXI slave ID width
    parameter int  AXIAWUW = 1,            // AXI slave AW user width
    parameter int  AXIWUW  = 1,            // AXI slave W user width
    parameter int  AXIBUW  = 1,            // AXI slave B user width
    parameter int  AXIARUW = 1,            // AXI slave AR user width
    parameter int  AXIRUW  = 1,            // AXI slave R user width
    parameter int  SYNCFB  = 0,            // AXI slave Sync flag base
    parameter int  SYNCFW  = 1,            // AXI slave Sync flag size
    parameter int  BC      = 0             // AXI use broadcase routine
    )
  (
   input  logic                                 clk,          // clock
   input  logic                                 rst_a,        // asynchronous reset, active high, synchronous deassertion
   input  logic [1:0]                           ptidx_a,      // GRPID
   // single AXI slave interface
   `AXINODATASLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface array
   `AXINODATAMSTN(NUMMST,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
   output logic [NUMMST:0]                      rgnt,      // response arbiter grant
   // address decoder inputs
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase,   // 4KB base address per aperture
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize,   // 4KB mask to specify aperture size
   input logic [NUMAP-1:0][NUMMST-1:0]          decmst     // onehot0 mast of the decoded master
   );
  //`VPOST_OFF
  // local parameters
  localparam int NML2 = $clog2(NUMMST);
  // local types
  typedef enum logic [1:0] { state_idle_e, state_data_e, state_resp_e } axi_state_t;
  typedef logic [4:0]        id_cnt_t;
  typedef logic [AXIIDW-1:0] id_t;
  typedef logic [NML2:0]     mst_t;
  typedef logic [NUMMST:0]   mst_oh_t;
  // local write datapath wires
  mst_oh_t                  wmst_sel;        // decoded write address, msb is error slave
  mst_t                     wmst_idx;        // decoded write address binary
  logic                     wfound;          // true if pending ID
  logic                     wcanissue;       // true if new write command can issue
  logic       [NUMID-1:0]   widx_inc;        // one-hot0 vector to increment pending transactions
  logic       [NUMID-1:0]   wpend_en;        // pending write valid&counter enble
  logic       [NUMID-1:0]   wmst_en;         // pending write master&id enble
  logic       [NUMID-1:0]   wpend_valid_r;   // pending ID valid
  id_cnt_t    [NUMID-1:0]   wpend_cnt_r;     // pending ID counter, max 31 transactions per ID
  logic       [NUMID-1:0]   wpend_valid_nxt; // pending ID valid, next
  id_cnt_t    [NUMID-1:0]   wpend_cnt_nxt;   // pending ID counter, max 31 transactions per ID, next
  id_t        [NUMID-1:0]   wpend_id_r;      // pending ID value
  mst_t       [NUMID-1:0]   wpend_mst_r;     // pending ID master index
  mst_oh_t                  bgnt;            // response arbiter grant
  logic                     bnxt;            // next arbitration
  logic                     wfifo_wval;      // write FIFO input valid
  logic                     wfifo_wacc;      // write FIFO input accept
  logic                     wfifo_rval;      // write FIFO output valid
  logic                     wfifo_racc;      // write FIFO output accept
  mst_t                     wfifo_rd;        // write FIFO output data
  logic                     axi_err_awvalid;
  logic                     axi_err_awready;
  logic                     axi_err_wvalid;
  logic                     axi_err_wready;
  logic                     axi_err_bvalid;
  logic                     axi_err_bready;
  axi_state_t               werr_state_nxt;  // write error state next
  axi_state_t               werr_state_r;    // write error state
  logic                     werr_state_en;
  logic                     werr_id_en;      // write error id
  id_t                      werr_id_r;
  // local read datapath wires
  mst_oh_t                  rmst_sel;        // decoded read address, msb is error slave
  mst_t                     rmst_idx;        // decoded read address binary
  logic                     rfound;          // true if pending ID
  logic                     rcanissue;       // true if new read command can issue
  logic       [NUMID-1:0]   ridx_inc;        // one-hot0 vector to increment pending transactions
  logic       [NUMID-1:0]   rpend_en;        // pending read valid&counter enble
  logic       [NUMID-1:0]   rmst_en;         // pending read master&id enble
  logic       [NUMID-1:0]   rpend_valid_r;   // pending ID valid
  id_cnt_t    [NUMID-1:0]   rpend_cnt_r;     // pending ID counter, max 31 transactions per ID
  logic       [NUMID-1:0]   rpend_valid_nxt; // pending ID valid, next
  id_cnt_t    [NUMID-1:0]   rpend_cnt_nxt;   // pending ID counter, max 31 transactions per ID, next
  id_t        [NUMID-1:0]   rpend_id_r;      // pending ID value
  mst_t       [NUMID-1:0]   rpend_mst_r;     // pending ID master index
  logic                     rnxt;            // next arbitration
  logic                     axi_err_arvalid;
  logic                     axi_err_arready;
  logic                     axi_err_rvalid;
  logic                     axi_err_rready;
  logic                     axi_err_rlast;
  axi_state_t               rerr_state_nxt;  // read error state next
  axi_state_t               rerr_state_r;    // read error state
  logic                     rerr_state_en;
  logic                     rerr_id_en;      // read error id
  id_t                      rerr_id_r;
  logic                     rerr_cnt_en;
  npu_axi_len_t             rerr_cnt_r;      // length counter
  npu_axi_len_t             rerr_cnt_nxt;    // length counter, next
  logic [SYNCFW-1:0]        arsyncflg;

  
  //////////////////////////////////////////////////////////////////////////////
  //
  // write datapath
  //
  //////////////////////////////////////////////////////////////////////////////
  

// spyglass disable_block W116
// SMD: OR bus should have equal assign width
// SJ: Left-handside MSB is the extra bit for error
  //
  // address decoder
  //
  // outputs: wmst_idx, wmst_sel
  always_comb
  begin : wdec_PROC
    // default outputs
    logic b;
    wmst_idx = '0;
    wmst_sel = '0;
    b = 1'b1;
    for (int a = 0; a < NUMAP; a++)
    begin
      if (b & ((decsize[a] & axi_slv_aw.addr[NPU_AXI_ADDR_W-1:12]) == decbase[a]))
      begin
        b = ~(|decmst[a]);
        wmst_sel |= decmst[a];
      end
    end
    for (int m = 0; m < NUMMST; m++)
    begin
      if (wmst_sel[m])
      begin
        wmst_idx |= unsigned'(m);
      end
    end
    if (wmst_sel == '0)
    begin
      // select err slave, index NUMMST
      wmst_sel = 1'b1 << NUMMST;
      wmst_idx = unsigned'(NUMMST);
    end
  end : wdec_PROC
// spyglass enable_block W116
    

  //
  // forward write commands
  //
  assign axi_mst_aw      = {NUMMST{axi_slv_aw}};
  assign axi_mst_awid    = {NUMMST{axi_slv_awid}};
  assign axi_mst_awuser  = {NUMMST{axi_slv_awuser}};
  assign wfifo_wval      = axi_slv_awvalid & axi_slv_awready;
  assign axi_slv_awready = wfifo_wacc & wcanissue & (|({axi_err_awready,axi_mst_awready} & wmst_sel) & (((wmst_idx == wfifo_rd) & wfifo_rval) | (!wfifo_rval)));
  always_comb
  begin : aw_PROC
    logic [NUMID-1:0] fnd;
    // default outputs
    axi_mst_awvalid = '0;
    axi_err_awvalid = 1'b0;
    wcanissue       = 1'b0;
    widx_inc        = '0;
    // check for a free entry in the table
    for (int i = 0; i < NUMID; i++)
    begin
      if (!(wcanissue | wpend_valid_r[i]))
      begin
        wcanissue   = 1'b1;
        widx_inc[i] = 1'b1;       
      end
    end
    // check if ID already exists in table
    for (int i = 0; i < NUMID; i++)
    begin
      fnd[i] = wpend_valid_r[i] && (wpend_id_r[i] == axi_slv_awid);
    end
    wfound = fnd != '0;
    if (wfound)
    begin
      widx_inc  = fnd;
      wcanissue = 1'b0;
    end
    // can only issue if target master matches and if counter does not overflow
    for (int i = 0; i < NUMID; i++)
    begin
      wcanissue |= fnd[i] & (wpend_cnt_r[i] != '1) && (wpend_mst_r[i] == wmst_idx);
    end
    if (axi_slv_awvalid & wfifo_wacc & wcanissue & (((wmst_idx == wfifo_rd) & wfifo_rval) | (!wfifo_rval)))
    begin
      {axi_err_awvalid,axi_mst_awvalid} = wmst_sel;
    end
  end : aw_PROC

  
  //
  // FIFO storing master index for write data
  //
  //`VPOST_ON
  npu_fifo
    #(
      .SIZE   ( 4            ),
      .DWIDTH ( $bits(mst_t) ),
      .FRCVAL ( 1'b0         ),
      .FRCACC ( 1'b0         )
      ) 
  u_wfifo_inst
    (
     .clk          ( clk        ),
     .rst_a        ( rst_a      ),
     .valid_write  ( wfifo_wval ),
     .accept_write ( wfifo_wacc ),
     .data_write   ( wmst_idx   ),
     .valid_read   ( wfifo_rval ),
     .accept_read  ( wfifo_racc ),
     .data_read    ( wfifo_rd   )
     );
  //`VPOST_OFF

  
  //
  // forward write data
  //
  assign axi_mst_wuser = {NUMMST{axi_slv_wuser}};
  assign axi_mst_wlast = {NUMMST{axi_slv_wlast}};
  assign wfifo_racc    = axi_slv_wvalid & axi_slv_wready & axi_slv_wlast;
  always_comb
  begin : w_PROC
    mst_oh_t s;
    // default outputs
    axi_mst_wvalid = 1'b0;
    axi_err_wvalid = 1'b0;
    axi_slv_wready = 1'b0;
    s = 1'b1<<wfifo_rd;
    if (wfifo_rval)
    begin
      // active write command
      {axi_err_wvalid,axi_mst_wvalid} = axi_slv_wvalid ? s : '0;
      axi_slv_wready = |({axi_err_wready,axi_mst_wready} & s);
    end
  end : w_PROC
  

  //
  // Return write response round-robin arbiter
  //
  npu_arb
  #(
    .NUM_REQ( $bits(mst_oh_t) ) 
  )
  u_bresp_arb
  (
   .clk   ( clk                             ),
   .rst_a ( rst_a                           ),
   .req   ( {axi_err_bvalid,axi_mst_bvalid} ),
   .gnt   ( bgnt                            ),
   .ok    ( bnxt                            )
  );
  // keep grant unless accepted
  assign bnxt     = axi_slv_bready || (~axi_slv_bvalid);
  
  
  //
  // Route write response
  //
  assign axi_slv_bvalid                  = |{axi_err_bvalid,axi_mst_bvalid};
  assign {axi_err_bready,axi_mst_bready} = axi_slv_bready ? bgnt : '0;
  always_comb
  begin : b_PROC
    // default outputs
    axi_slv_bid   = '0;
    axi_slv_buser = '0;
    axi_slv_bresp = npu_axi_resp_t'(0);
    // go over master ports to implement OR bus
    for (int m = 0; m < NUMMST; m++)
    begin
      if (bgnt[m])
      begin
        axi_slv_bid   |= axi_mst_bid[m];
        axi_slv_bresp  = npu_axi_resp_t'(axi_slv_bresp | axi_mst_bresp[m]);
        axi_slv_buser |= axi_mst_buser[m];
      end
    end
    if (bgnt[NUMMST])
    begin
      axi_slv_bid   |= werr_id_r;
      axi_slv_bresp  = npu_axi_resp_t'(axi_slv_bresp | npu_axi_resp_decerr_e);
      axi_slv_buser |= '0;
    end
  end : b_PROC


  //
  // Track write transactions
  //
  always_comb
  begin : wcnt_PROC
    // default outputs
    wpend_en        = '0;
    wmst_en         = '0;
    wpend_valid_nxt = wpend_valid_r;
    wpend_cnt_nxt   = wpend_cnt_r;
    if (axi_slv_awvalid & axi_slv_awready)
    begin
      for (int i = 0; i < NUMID; i++)
      begin
        if (widx_inc[i])
        begin
          wpend_en[i]        = 1'b1;
          wpend_cnt_nxt[i]   = wpend_cnt_nxt[i] + 1'b1;
          wpend_valid_nxt[i] = 1'b1;
        end
      end
      if (!wfound)
      begin
        wmst_en = widx_inc;
      end
    end
    if (axi_slv_bvalid & axi_slv_bready)
    begin
      // search for ID
      for (int i = 0; i < NUMID; i++)
      begin
        if (wpend_valid_r[i] && (wpend_id_r[i] == axi_slv_bid))
        begin
          // found ID in table, subtract from pending
          wpend_en[i]        = 1'b1;
          wpend_valid_nxt[i] = wpend_cnt_nxt[i] != 'd1;
          wpend_cnt_nxt[i]   = wpend_cnt_nxt[i] - 1'b1;
        end
      end
    end
  end : wcnt_PROC

  
  //
  // Write decoding error
  //
  always_comb
  begin : werr_PROC
    // default outputs
    werr_state_nxt  = state_idle_e;
    werr_id_en      = 1'b0;
    werr_state_en   = 1'b0;
    axi_err_awready = 1'b0;
    axi_err_wready  = 1'b0;
    axi_err_bvalid  = 1'b0;
    case (werr_state_r)
    state_resp_e:
      begin
        axi_err_bvalid  = 1'b1;
        if (axi_err_bready)
        begin
          werr_state_en  = 1'b1;
          werr_state_nxt = state_idle_e;
        end
      end
    state_data_e:
      begin
        // accept write data
        axi_err_wready = 1'b1;
        if (axi_err_wvalid & axi_slv_wlast)
        begin
          werr_state_en  = 1'b1;
          werr_state_nxt = state_resp_e;
        end
      end
    default: // state_idle_e:
      begin
        // accept erroneous command
        axi_err_awready = 1'b1;
        if (axi_err_awvalid)
        begin
          werr_id_en     = 1'b1;
          werr_state_en  = 1'b1;
          werr_state_nxt = state_data_e;
        end
      end
    endcase // case (werr_state_r)
  end : werr_PROC


  //
  // Update write state
  //
  always_ff @(posedge clk or posedge rst_a)
  begin : wstate_reg_PROC
    if (rst_a == 1'b1)
    begin
      werr_state_r  <= state_idle_e;
      werr_id_r     <= '0;
      wpend_valid_r <= '0;
      wpend_cnt_r   <= '0;
      wpend_mst_r   <= '0;
      wpend_id_r    <= '0;
    end
    else
    begin
      if (werr_state_en)
      begin
        werr_state_r <= werr_state_nxt;
      end
      if (werr_id_en)
      begin
        werr_id_r    <= axi_slv_awid;
      end
      for (int i = 0; i < NUMID; i++)
      begin
        if (wpend_en[i])
        begin
          wpend_valid_r[i] <= wpend_valid_nxt[i];
          wpend_cnt_r[i]   <= wpend_cnt_nxt[i];
        end
        if (wmst_en[i])
        begin
          wpend_mst_r[i] <= wmst_idx;
          wpend_id_r[i]  <= axi_slv_awid;
        end
      end
    end
  end : wstate_reg_PROC



  //////////////////////////////////////////////////////////////////////////////
  //
  // read datapath
  //
  //////////////////////////////////////////////////////////////////////////////
  
// spyglass disable_block W116
// SMD: OR bus should have equal assign width
// SJ: Left-handside MSB is the extra bit for error
  //
  // address decoder
  //
  // outputs: rmst_idx, rmst_sel
  always_comb
  begin : rdec_PROC
    // default outputs
    logic b;
    rmst_idx = '0;
    rmst_sel = '0;
    b = 1'b1;
    if (BC)
    begin
      arsyncflg     =  axi_slv_aruser[SYNCFB+:SYNCFW];
      for (int a = 0; a < NUMAP-1; a++)
      begin
        if (b & ((decsize[a] & axi_slv_ar.addr[NPU_AXI_ADDR_W-1:12]) == decbase[a]))
        begin
          b = ~(|decmst[a]);
          rmst_sel |= decmst[a];
        end
      end
      // Force to use sync request for NoC
      if (b & ((decsize[NUMAP-1] & axi_slv_ar.addr[NPU_AXI_ADDR_W-1:12]) == decbase[NUMAP-1]))
      begin
        if (arsyncflg != '0) begin
          if (ptidx_a == 2'd0) begin
            casez (arsyncflg)
            4'b???1: rmst_sel |= 'd1;
            default: rmst_sel |= 'd0; // Error in sync flag
            endcase
          end
          else if (ptidx_a == 2'd1) begin
            casez (arsyncflg)
            4'b???1: rmst_sel |= 'd2;
            4'b??10: rmst_sel |= 'd1;
            default: rmst_sel |= 'd0; // Error in sync flag
            endcase
          end
          else if (ptidx_a == 2'd2) begin
            casez (arsyncflg)
            4'b???1: rmst_sel |= 'd4;
            4'b??10: rmst_sel |= 'd8;
            4'b?100: rmst_sel |= 'd1;
            default: rmst_sel |= 'd0; // Error in sync flag
            endcase
          end
          else begin // (ptidx_a == 2'd3)
            casez (arsyncflg)
            4'b???1: rmst_sel |= 'd8;
            4'b??10: rmst_sel |= 'd4;
            4'b?100: rmst_sel |= 'd2;
            default: rmst_sel |= 'd0; // Error in sync flag
            endcase
          end
        end
        else begin
          rmst_sel |= decmst[NUMAP-1];
        end
      end
    end
    else 
    begin
      for (int a = 0; a < NUMAP; a++)
      begin
        if (b & ((decsize[a] & axi_slv_ar.addr[NPU_AXI_ADDR_W-1:12]) == decbase[a]))
        begin
          b = ~(|decmst[a]);
          rmst_sel |= decmst[a];
        end
      end
    end
    for (int m = 0; m < NUMMST; m++)
    begin
      if (rmst_sel[m])
      begin
        rmst_idx |= unsigned'(m);
      end
    end
    if (rmst_sel == '0)
    begin
      // select err slave, index NUMMST
      rmst_sel = 1'b1 << NUMMST;
      rmst_idx = unsigned'(NUMMST);
    end
  end : rdec_PROC
// spyglass enable_block W116
  

  //
  // forward read commands
  //
  assign axi_mst_ar      = {NUMMST{axi_slv_ar}};
  assign axi_mst_arid    = {NUMMST{axi_slv_arid}};
  assign axi_mst_aruser  = {NUMMST{axi_slv_aruser}};
  assign axi_slv_arready = rcanissue & (|({axi_err_arready,axi_mst_arready} & rmst_sel));
  always_comb
  begin : ar_PROC
    logic [NUMID-1:0] fnd;
    // default outputs
    axi_mst_arvalid = '0;
    axi_err_arvalid = 1'b0;
    rcanissue       = 1'b0;
    ridx_inc        = '0;
    // check for a free entry in the table
    for (int i = 0; i < NUMID; i++)
    begin
      if (!(rcanissue | rpend_valid_r[i]))
      begin
        rcanissue   = 1'b1;
        ridx_inc[i] = 1'b1;       
      end
    end
    // check if ID already exists in table
    for (int i = 0; i < NUMID; i++)
    begin
      fnd[i] = rpend_valid_r[i] && (rpend_id_r[i] == axi_slv_arid);
    end
    rfound = fnd != '0;
    if (rfound)
    begin
      ridx_inc  = fnd;
      rcanissue = 1'b0;
    end
    // can only issue if target master matches and if counter does not overflow
    for (int i = 0; i < NUMID; i++)
    begin
      rcanissue |= fnd[i] & (rpend_cnt_r[i] != '1) && (rpend_mst_r[i] == rmst_idx);
    end
    if (axi_slv_arvalid & rcanissue)
    begin
      {axi_err_arvalid,axi_mst_arvalid} = rmst_sel;
    end
  end : ar_PROC

  
  //
  // Return read response round-robin arbiter
  //
  npu_arb
  #(
    .NUM_REQ( $bits(mst_oh_t) )
  )
  u_rresp_arb
  (
   .clk   ( clk                             ),
   .rst_a ( rst_a                           ),
   .req   ( {axi_err_rvalid,axi_mst_rvalid} ),
   .gnt   ( rgnt                            ),
   .ok    ( rnxt                            )
  );
  // keep grant unless accepted
  assign rnxt     = axi_slv_rready || (~axi_slv_rvalid);

  
  //
  // Route read response
  //
  assign axi_slv_rvalid                  = |{axi_err_rvalid,axi_mst_rvalid};
  assign {axi_err_rready,axi_mst_rready} = axi_slv_rready ? rgnt : '0;
  always_comb
  begin : r_PROC
    // default outputs
    axi_slv_rid   = '0;
    axi_slv_rlast = 1'b0;
    axi_slv_ruser = '0;
    axi_slv_rresp = npu_axi_resp_t'(0);
    // go over master ports to implement OR bus
    for (int m = 0; m < NUMMST; m++)
    begin
      if (rgnt[m])
      begin
        axi_slv_rid   |= axi_mst_rid[m];
        axi_slv_rlast |= axi_mst_rlast[m];
        axi_slv_rresp  = npu_axi_resp_t'(axi_slv_rresp | axi_mst_rresp[m]);
        axi_slv_ruser |= axi_mst_ruser[m];
      end
    end
    if (rgnt[NUMMST])
    begin
      axi_slv_rid   |= rerr_id_r;
      axi_slv_rlast |= axi_err_rlast;
      axi_slv_rresp  = npu_axi_resp_t'(axi_slv_rresp | npu_axi_resp_decerr_e);
      axi_slv_ruser |= '0;
    end
  end : r_PROC

  
  //
  // Track read transactions
  //
  always_comb
  begin : rcnt_PROC
    // default outputs
    rpend_en        = '0;
    rmst_en         = '0;
    rpend_valid_nxt = rpend_valid_r;
    rpend_cnt_nxt   = rpend_cnt_r;
    if (axi_slv_arvalid & axi_slv_arready)
    begin
      for (int i = 0; i < NUMID; i++)
      begin
        if (ridx_inc[i])
        begin
          rpend_en[i]        = 1'b1;
          rpend_cnt_nxt[i]   = rpend_cnt_nxt[i] + 1'b1;
          rpend_valid_nxt[i] = 1'b1;
        end
      end
      if (!rfound)
      begin
        rmst_en = ridx_inc;
      end
    end
    if (axi_slv_rvalid & axi_slv_rready & axi_slv_rlast)
    begin
      // search for ID
      for (int i = 0; i < NUMID; i++)
      begin
        if (rpend_valid_r[i] && (rpend_id_r[i] == axi_slv_rid))
        begin
          // found ID in table, subtract from pending
          rpend_en[i]        = 1'b1;
          rpend_valid_nxt[i] = rpend_cnt_nxt[i] != 'd1;
          rpend_cnt_nxt[i]   = rpend_cnt_nxt[i] - 1'b1;
        end
      end
    end
  end : rcnt_PROC

  
  //
  // Read decoding error
  //
  assign axi_err_rlast = rerr_cnt_r == '0;
  always_comb
  begin : rerr_PROC
    // default outputs
    rerr_state_nxt  = state_idle_e;
    rerr_id_en      = 1'b0;
    rerr_state_en   = 1'b0;
    axi_err_arready = 1'b0;
    axi_err_rvalid  = 1'b0;
    rerr_cnt_en     = 1'b0;
    rerr_cnt_nxt    = rerr_cnt_r - 1'b1;
    case (rerr_state_r)
    state_data_e:
      begin
        // return read data
        axi_err_rvalid = 1'b1;
        rerr_cnt_en = axi_err_rready;
        if (axi_err_rready & axi_err_rlast)
        begin
          rerr_state_en  = 1'b1;
          rerr_state_nxt = state_idle_e;
        end
      end
    default: // state_idle_e:
      begin
        // accept erroneous command
        axi_err_arready = 1'b1;
        rerr_cnt_nxt = axi_slv_ar.len;
        if (axi_err_arvalid)
        begin
          rerr_cnt_en    = 1'b1;
          rerr_id_en     = 1'b1;
          rerr_state_en  = 1'b1;
          rerr_state_nxt = state_data_e;
        end
      end
    endcase // case (rerr_state_r)
  end : rerr_PROC


  //
  // Update read state
  //
  always_ff @(posedge clk or posedge rst_a)
  begin : rstate_reg_PROC
    if (rst_a == 1'b1)
    begin
      rerr_state_r         <= state_idle_e;
      rerr_id_r            <= '0;
      rerr_cnt_r           <= '0;
      rpend_valid_r        <= '0;
      rpend_cnt_r          <= '0;
      rpend_mst_r          <= '0;
      rpend_id_r           <= '0;
    end
    else
    begin
      if (rerr_state_en)
      begin
        rerr_state_r       <= rerr_state_nxt;
      end
      if (rerr_id_en)
      begin
        rerr_id_r          <= axi_slv_arid;
      end
      if (rerr_cnt_en)
      begin
        rerr_cnt_r         <= rerr_cnt_nxt;
      end
      for (int i = 0; i < NUMID; i++)
      begin
        if (rpend_en[i])
        begin
          rpend_valid_r[i] <= rpend_valid_nxt[i];
          rpend_cnt_r[i]   <= rpend_cnt_nxt[i];
        end
        if (rmst_en[i])
        begin
          rpend_mst_r[i]   <= rmst_idx;
          rpend_id_r[i]    <= axi_slv_arid;
        end
      end
    end
  end : rstate_reg_PROC
  
`ifdef ABV_ON
  // assertions
  property pcfg;
  @(rst_a)  NUMID <= (1<<AXIIDW);
  endproperty : pcfg
  assert property (pcfg) else $warning("Warning: ID tracking overconfigured");  
`endif

endmodule : npu_axi_demux_ctrl
