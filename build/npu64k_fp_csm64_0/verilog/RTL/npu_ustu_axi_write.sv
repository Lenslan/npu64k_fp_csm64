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
// Top-level file for the AXI write 
//

`include "npu_axi_macros.svh"

module npu_ustu_axi_write
  import npu_types::*;
  #(
    // AXI data with XM
    parameter AXI_MST_IDW = 1,
    parameter MAXIAWUW    = 1,             // AXI MMIO slave AW user width
    parameter MAXIWUW     = 1,             // AXI MMIO slave W user width
    parameter MAXIBUW     = 1,             // AXI MMIO slave B user width
    parameter MAXIARUW    = 1,             // AXI MMIO slave AR user width
    parameter MAXIRUW     = 1,             // AXI MMIO slave R user width
    parameter BUFFER_SIZE = 1024,
    parameter AXI_OST  = 16,
    parameter STU_D    = 512
   )
  (
   // interfaces
   //
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   `AXIWMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,dma_daxi_),  // AXI data transfer, write only
// spyglass enable_block W240
   // XM read request
   input  logic                    xm_w_valid,
   input  xm_buf_t                 xm_w_request,    // xm_len_t len: [31:0]; xm_ptr_t base: [ASIE-1:0];
   output logic                    xm_w_accept,
   input  logic                    boost,
   input  logic [1:0]              ost_cfg,
   
   output logic                    buffer_rd_accept,
   output logic [5:0]              buffer_rd_num,
   output logic [5:0]              buffer_rd_alsb,
   input  logic [511:0]            buffer_rd_data,
   input  logic [15:0]             buffer_vld_size,

   input  logic [64-1: 0]     vmid,
   output logic                    idle,            //AXI write is idle
   output logic                    err_st,          //AXI write got error response

   // clock and reset
   //
   input  logic                    clk,                    // clock, all logic clocked at posedge
   input  logic                    rst_dp                  // asynchronous reset, active high
   );

  // Parameters
  localparam int AXI_ALSB      = $clog2(STU_D/8);
  localparam int FUL_BSIZE     = STU_D*2;
  localparam int MAX_BSIZE     = BUFFER_SIZE/4;
  localparam int FUL_WLEN      = $clog2(FUL_BSIZE*8/STU_D);
  localparam int AXI_WLEN      = $clog2(MAX_BSIZE*8/STU_D);
  localparam int BUF_WSTRB     = STU_D/8;
  localparam int ENTRIES_WIDTH = $clog2(AXI_OST);
  localparam int CMD_SZ        = $bits(axi_cmd_t);
  localparam int BFIFO_SIZE    = AXI_OST*2;

  typedef struct packed {
    logic [8:0]                    shamt;      //burst shift
    logic [8:0]                    lst_len;    //last beat len 
    logic                          fstr;       //first trans flag
    logic [FUL_WLEN-1:0]           lent;       //Beats count to generate wlast
  } axi_wop_t;

  typedef axi_wop_t  [AXI_OST-1:0]  wop_t;

// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow
  function automatic void xm_cmd_gen(input xm_buf_t xm_cmd_in, input logic boost, output axi_cmd_t xm_cmd_out);
    xm_len_t             len_t;
    xm_len_t             awlenb;
    logic [AXI_ALSB-1:0] pad_msk;
    logic [ASIZE-1:0]    addr_msk;
    logic [ASIZE-1:0]    len_msk;

    // address aligned to 512b
    addr_msk        =  ~((1<<AXI_ALSB) - 1);
    len_msk         =   ( 1<<AXI_ALSB) - 1 ;
    pad_msk         =   ( 1<<AXI_ALSB) - 1 ;
    awlenb          =   '0;

    // split transfer with 0x400 (1024Bytes) Boundary
    // Proposed maximum burst arlen
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Has default value, and RHS is the real size
    if (FUL_WLEN > AXI_WLEN) begin
      awlenb  =  boost ? {(~xm_cmd_in.base[AXI_ALSB+:FUL_WLEN]),pad_msk} : {(~xm_cmd_in.base[AXI_ALSB+:AXI_WLEN]),pad_msk};
    end
    else begin
      awlenb  =  {(~xm_cmd_in.base[AXI_ALSB+:FUL_WLEN]),pad_msk};
    end
// spyglass enable_block W164b

    // HW total length
    len_t = xm_cmd_in.len + (xm_cmd_in.base & len_msk) - 1;

    if (awlenb < len_t) begin
      xm_cmd_out.xm_bcmd.len  = awlenb;
      xm_cmd_out.xm_bcmd.padm = 0;
      xm_cmd_out.xm_bcmd.base = (xm_cmd_in.base & addr_msk);
      xm_cmd_out.xm_ncmd.len  = len_t - awlenb;
      xm_cmd_out.xm_ncmd.padm = 0;
      xm_cmd_out.xm_ncmd.base = (xm_cmd_in.base & addr_msk) + awlenb + 1;
      xm_cmd_out.shamt        = (xm_cmd_in.base & len_msk);
      xm_cmd_out.lst          = 1'b0;
      xm_cmd_out.lst_len      = (awlenb == 32'd63) ? (9'd63 - (xm_cmd_in.base & len_msk)) : 9'd63;
    end
    else begin
      xm_cmd_out.xm_bcmd.len  = len_t;
      xm_cmd_out.xm_bcmd.padm = 0;
      xm_cmd_out.xm_bcmd.base = (xm_cmd_in.base & addr_msk);
      xm_cmd_out.xm_ncmd.len  = 0;
      xm_cmd_out.xm_ncmd.padm = 0;
      xm_cmd_out.xm_ncmd.base = 0;
      xm_cmd_out.shamt        = (xm_cmd_in.base & len_msk);
      xm_cmd_out.lst          = 1;
// spyglass disable_block W116
//SMD:Width mismatch
//SJ :No overflow
      xm_cmd_out.lst_len      = (len_t < 32'd64) ? (xm_cmd_in.len - 1) : (len_t & len_msk);
// spyglass enable_block W116
    end
  endfunction : xm_cmd_gen
// spyglass enable_block W164a

  // Local parameters
  typedef enum logic [1:0] { 
    npu_axi_status_idle_e,  // issue state is idle
    npu_axi_status_issue_e  // issue the xm seq 
  } npu_axi_state_t;

  // Registers
  // Data collection
  logic [FUL_WLEN-1:0]             wlent_r;    // Write AXI counter
  logic [FUL_WLEN-1:0]             wlent_nxt;
  logic                            wlent_en;
  // wop ptr
  logic [ENTRIES_WIDTH:0]          wop_rd_ptr_r;
  logic [ENTRIES_WIDTH:0]          wop_rd_ptr_nxt;
  logic                            wop_rd_ptr_en;

  logic [ENTRIES_WIDTH:0]          wop_wr_ptr_r;
  logic [ENTRIES_WIDTH:0]          wop_wr_ptr_nxt;
  logic                            wop_wr_ptr_en;

  // wop entries
  wop_t                            wop_r;
  wop_t                            wop_nxt;
  logic [AXI_OST-1:0]              wop_en;

  logic                            b_push;
  logic                            b_push_accept;
  logic                            b_valid;
  logic                            b_pop;

  logic [ENTRIES_WIDTH:0]          wop_mask;
  logic [ENTRIES_WIDTH:0]          wop_full;

  // FSM
  npu_axi_state_t                  npu_axi_state_r;
  npu_axi_state_t                  npu_axi_state_nxt;
  logic                            npu_axi_state_en;

  // Pushed Command
  axi_cmd_t                        xm_cmd_r;
  axi_cmd_t                        xm_cmd_nxt;
  logic                            xm_cmd_en;

  // AXI write error response
  logic                            xm_err_r;
  logic                            xm_err_nxt;
  logic                            xm_err_en;

  logic                            xm_boost_r;
  logic                            xm_boost_nxt;
  logic                            xm_boost_en;

  // Wires
  // Last issued
  logic                            lst_issued;
  logic                            lst_beat;
  logic [BUF_WSTRB-1:0]            i_wmsk_mux_a;

  logic [15:0]                     buffer_alloc_r;
  logic [15:0]                     buffer_alloc_nxt;
  logic                            buffer_alloc_en;

  logic [STU_D-1:0]                axi_wdata_mask;

  // Command & Package Update
generate
if(FUL_WLEN > AXI_WLEN) begin : PROC_WOP_AXI_GT
  always_comb
  begin : dma_wop_axi_lent_GT_PROC
    b_push                 = 1'b0;
    for (int n = 0; n < AXI_OST; n++)
    begin
          wop_nxt[n].lent = wop_r[n].lent;
    end

// spyglass disable_block W362
// SMD: LHS width is less than RHS
// SJ: Reviewed
    if (npu_axi_state_r == npu_axi_status_issue_e) begin
      if ((((wop_rd_ptr_r ^ wop_wr_ptr_r) & wop_mask) != wop_full) && // WOP entries not full
          b_push_accept  && //Bresp is already released in target entry 
          (xm_boost_r || ((buffer_vld_size - buffer_alloc_r) > (xm_cmd_r.xm_bcmd.len - xm_cmd_r.shamt))) //Burst Size Limitation to require data before write (Skip in Boost Mode)
         )
// spyglass enable_block W362
      begin
        if (dma_daxi_awready == 1'b1) begin
            wop_nxt[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]].lent    = xm_boost_r ? xm_cmd_r.xm_bcmd.len[AXI_ALSB+:FUL_WLEN] : {{(FUL_WLEN-AXI_WLEN){1'b0}}, xm_cmd_r.xm_bcmd.len[AXI_ALSB+:AXI_WLEN]};
            // Push bresp op pending
            b_push          = 1'b1;
        end
      end
    end
  end
end else begin:  PROC_WOP_AXI_NGT
  always_comb
  begin : dma_wop_axi_lent_NGT_PROC
    b_push                 = 1'b0;
    for (int n = 0; n < AXI_OST; n++)
    begin
          wop_nxt[n].lent = wop_r[n].lent;
    end

// spyglass disable_block W362
// SMD: LHS width is less than RHS
// SJ: Reviewed
    if (npu_axi_state_r == npu_axi_status_issue_e) begin
      if ((((wop_rd_ptr_r ^ wop_wr_ptr_r) & wop_mask) != wop_full) && // WOP entries not full
          b_push_accept  && //Bresp is already released in target entry 
          (xm_boost_r || ((buffer_vld_size - buffer_alloc_r) > (xm_cmd_r.xm_bcmd.len - xm_cmd_r.shamt))) //Burst Size Limitation to require data before write (Skip in Boost Mode)
         )
// spyglass enable_block W362
      begin
        if (dma_daxi_awready == 1'b1) begin
            wop_nxt[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]].lent    = xm_cmd_r.xm_bcmd.len[AXI_ALSB+:FUL_WLEN];
            // Push bresp op pending
            b_push          = 1'b1;
        end
      end
    end
  end
end
endgenerate


// spyglass disable_block W164a
// SMD: LHS width is less than RHS
// SJ: Reviewed
  // Command & Package Update
  always_comb
  begin : dma_wop_axi_PROC
    xm_cmd_en              = 1'b0;
    xm_cmd_nxt             = xm_cmd_r;
    xm_err_en              = 1'b0;
    xm_err_nxt             = xm_err_r;
    xm_boost_en            = 1'b0;
    xm_boost_nxt           = xm_boost_r;
    lst_issued             = 1'b0;
    dma_daxi_awvalid       = 1'b0;
    dma_daxi_awid          = 1'b0;
    dma_daxi_aw.addr       = '0;
    dma_daxi_aw.cache      = 4'b0010;   // modifiable non-bufferable
    dma_daxi_aw.prot       = 3'b010; // unprivileged, non-secure, data access
    dma_daxi_aw.lock       = npu_axi_lock_normal_e;
    dma_daxi_aw.burst      = npu_axi_burst_incr_e;
    dma_daxi_aw.len        = 8'h00;
    dma_daxi_aw.size       = 3'd6;   // 512b data
    dma_daxi_aw.region     = '0;   
    dma_daxi_wvalid        = 1'b0;
    dma_daxi_wdata         = 'b0;
    dma_daxi_wstrb         = 'b0;
    dma_daxi_wlast         = lst_beat;
    dma_daxi_bready        = 1'b1;   // always accept bresp
    dma_daxi_awuser        = '0;
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Has default value, and STU doesn't has BDMA field
    dma_daxi_awuser        = vmid;
// spyglass enable_block W164b
    dma_daxi_wuser         = '0;

    wop_wr_ptr_en          = 1'b0;
    wop_wr_ptr_nxt         = wop_wr_ptr_r;
    wop_rd_ptr_en          = 1'b0;
    wop_rd_ptr_nxt         = wop_rd_ptr_r;
    wop_en                 = 'b0;
    //wop_nxt                = wop_r;
    for (int n = 0; n < AXI_OST; n++)
      begin
          wop_nxt[n].shamt = wop_r[n].shamt;
          wop_nxt[n].lst_len = wop_r[n].lst_len;
          wop_nxt[n].fstr = wop_r[n].fstr;
      end

    wlent_en               = 1'b0;
    wlent_nxt              = wlent_r;
    b_pop                  = 1'b0;

    i_wmsk_mux_a           = 'b0;

    buffer_rd_accept       = 'b0;
    buffer_rd_num          = 'b0; 
    buffer_rd_alsb         = 'b0;
    buffer_alloc_nxt       = buffer_alloc_r;
    buffer_alloc_en        = 'b0;
    axi_wdata_mask         = 'b0;
    wop_mask               = '0;
    wop_full               = '0;

    case (ost_cfg)
      2'b01: // up to 50% AXI_OST -> 16
        begin 
          wop_full = {2'b1, {(ENTRIES_WIDTH-1){1'b0}}}; 
          wop_mask = {1'b0, {(ENTRIES_WIDTH  ){1'b1}}};  
        end
      2'b10: // up to 25% AXI_OST -> 8
        begin 
          wop_full = {3'b1, {(ENTRIES_WIDTH-2){1'b0}}}; 
          wop_mask = {2'b0, {(ENTRIES_WIDTH-1){1'b1}}};
        end
      2'b11: // up to 12.5% AXI_OST -> 4
        begin 
          wop_full = {4'b1, {(ENTRIES_WIDTH-3){1'b0}}}; 
          wop_mask = {3'b0, {(ENTRIES_WIDTH-2){1'b1}}};  
        end
      default: // up to AXI_OST -> 32
        begin 
          wop_full = {1'b1, {ENTRIES_WIDTH{1'b0}}};
          wop_mask = {      {(ENTRIES_WIDTH+1){1'b1}}};
        end
    endcase

    // Initialize issue
    if ((npu_axi_state_r == npu_axi_status_idle_e) && (xm_w_valid) && 
        ((wop_rd_ptr_r == wop_wr_ptr_r) || ((wop_rd_ptr_r[0] != wop_wr_ptr_r[0]) && lst_beat))
       ) begin
      // Initialize burst command
      xm_cmd_en              =   1'b1;
      xm_cmd_gen(xm_w_request, boost, xm_cmd_nxt);
      xm_boost_en            = 1'b1;
      xm_boost_nxt           = boost;
    end
    if (npu_axi_state_r == npu_axi_status_issue_e) begin
// spyglass disable_block SelfDeterminedExpr-ML W362
//SMD:Self determined and width mismatch
//SJ :Ignore self determine and width mismatch (buffer_vld_size - buffer_alloc_r) > (xm_cmd_r.xm_bcmd.len - xm_cmd_r.shamt)
      if ((((wop_rd_ptr_r ^ wop_wr_ptr_r) & wop_mask) != wop_full) && // WOP entries not full
          b_push_accept  && //Bresp is already released in target entry 
          (xm_boost_r || ((buffer_vld_size - buffer_alloc_r) > (xm_cmd_r.xm_bcmd.len - xm_cmd_r.shamt))) //Burst Size Limitation to require data before write (Skip in Boost Mode)
         )
// spyglass enable_block SelfDeterminedExpr-ML W362
      begin
        dma_daxi_awvalid  = 1'b1;
        dma_daxi_aw.addr  = xm_cmd_r.xm_bcmd.base;
        dma_daxi_aw.len   = xm_cmd_r.xm_bcmd.len[31:AXI_ALSB];
        if (dma_daxi_awready == 1'b1) begin
          // Push Write OP into Buffer
          wop_wr_ptr_en           =  1'b1;
          wop_wr_ptr_nxt          =  wop_wr_ptr_r + 1;
          wop_en[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]]          = 1'b1;
          wop_nxt[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]].shamt   = xm_cmd_r.shamt;
          wop_nxt[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]].lst_len = xm_cmd_r.lst_len;
          wop_nxt[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]].fstr    = 1'b1;
          //wop_nxt[wop_wr_ptr_r[ENTRIES_WIDTH-1:0]].lent    = xm_cmd_r.xm_bcmd.len[AXI_ALSB+:AXI_WLEN];

          // Update Command
          xm_cmd_en           = 1'b1;
          xm_cmd_gen(xm_cmd_r.xm_ncmd, xm_boost_r, xm_cmd_nxt);
          lst_issued          = (xm_cmd_r.lst == 1'b1);
// spyglass disable_block W116
//SMD:Expression width mismatch (-)
//SJ :Ignore width mismatch with xm_cmd_r.xm_bcmd.len, no overflow
          buffer_alloc_nxt    = buffer_alloc_nxt + xm_cmd_r.xm_bcmd.len + 1 - xm_cmd_r.shamt;
// spyglass enable_block W116
          buffer_alloc_en     = 'b1;
        end
      end
    end

    //Check wdata
    //Step 1. set ALSB and valid bytes
    if (wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].fstr) begin
      buffer_rd_num  = lst_beat ? wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].lst_len 
                                : (9'd63 - wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].shamt);
      buffer_rd_alsb = wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].shamt;
    end
    else begin
      buffer_rd_num  = lst_beat ? wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].lst_len 
                                : 9'd63;
      buffer_rd_alsb = 'b0;
    end

    //Step 2. Generate WSTRB
    for (int n = 0; n < BUF_WSTRB; n++)
    begin
      if (wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].fstr) begin
        if (wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].shamt > n) begin
          i_wmsk_mux_a[n] = 1'b0;
          axi_wdata_mask[8*n+:8] = 8'h00;
        end
        else if (lst_beat) begin
          if (n <= (wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].shamt + wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].lst_len)) begin
            i_wmsk_mux_a[n] = 1'b1;
            axi_wdata_mask[8*n+:8] = 8'hFF;
          end
          else begin
            i_wmsk_mux_a[n] = 1'b0;
            axi_wdata_mask[8*n+:8] = 8'h00;
          end
        end
        else begin
          i_wmsk_mux_a[n] = 1'b1;
          axi_wdata_mask[8*n+:8] = 8'hFF;
        end
      end
      else begin
        if (lst_beat) begin
          if (n <= (wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].lst_len)) begin
            i_wmsk_mux_a[n] = 1'b1;
            axi_wdata_mask[8*n+:8] = 8'hFF;
          end
          else begin
            i_wmsk_mux_a[n] = 1'b0;
            axi_wdata_mask[8*n+:8] = 8'h00;
          end
        end
        else begin
          i_wmsk_mux_a[n] = 1'b1;
          axi_wdata_mask[8*n+:8] = 8'hFF;
        end
      end
    end

    //Step 3. Write wdata: 1. pending command is available; 2. Enough data to write
// spyglass disable_block W362
// SMD:width mismatch
// SJ :Ignore buffer_vld_size > buffer_rd_num width mismatch, no influence on function
    if ((buffer_vld_size > buffer_rd_num) && (wop_rd_ptr_r != wop_wr_ptr_r)) begin
// spyglass enable_block W362
      dma_daxi_wvalid     =  1'b1;
      dma_daxi_wdata      =  buffer_rd_data[STU_D-1:0] & axi_wdata_mask;
      dma_daxi_wstrb      =  i_wmsk_mux_a;
      if (dma_daxi_wready) begin
        buffer_rd_accept = 1'b1;
        // Release alloc
// spyglass disable_block W116
//SMD:Expression width mismatch (-)
//SJ :Ignore width mismatch with xm_cmd_r.xm_bcmd.len, no overflow
        buffer_alloc_nxt = buffer_alloc_nxt - buffer_rd_num - 1;
// spyglass enable_block W116
        buffer_alloc_en  = 1'b1;
        if (wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].fstr) begin
          // Disable first flag
          wop_en[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]]          = 1'b1;
          wop_nxt[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].fstr    = 1'b0;
        end
        if (lst_beat == 1'b1) begin
          // current burst done, update bresp entry, move to next wop
          wlent_en        = 1'b1;
          wlent_nxt       =  'b0;
          wop_rd_ptr_en   = 1'b1;
          wop_rd_ptr_nxt  = wop_rd_ptr_r + 1;
        end
        else begin
          // increase wdata counter
          wlent_en        = 1'b1;
          wlent_nxt       = wlent_r + 1;
        end
      end
    end

    //Step 4. Update bresp table
    if ((dma_daxi_bvalid == 1'b1) && (b_valid)) begin
      b_pop                     = 1'b1;
      xm_err_en                 = 1'b1;
      xm_err_nxt                = ((dma_daxi_bresp != npu_axi_resp_okay_e) && (dma_daxi_bresp != npu_axi_resp_exokay_e));
    end

    if (xm_err_r == 1'b1) begin
      xm_err_en                 = 1'b1;
      xm_err_nxt                = 1'b0;
    end

  end : dma_wop_axi_PROC
// spyglass enable_block W164a

  //
  // AXI write next state
  //
  always_comb
  begin : npu_axi_nxt_PROC
    npu_axi_state_en  = 1'b0;
    npu_axi_state_nxt = npu_axi_state_r;
    xm_w_accept       = 1'b0;
    casez (npu_axi_state_r)
      npu_axi_status_issue_e:
        begin
          if (lst_issued) begin
            npu_axi_state_en  = 1'b1;
            npu_axi_state_nxt = npu_axi_status_idle_e;
          end
          else begin
            npu_axi_state_en  = 1'b1;
            npu_axi_state_nxt = npu_axi_status_issue_e;
          end
        end
      default: // npu_axi_status_idle_e
        begin
          // idle, wait for next request
          if (xm_w_valid && 
              ((wop_rd_ptr_r == wop_wr_ptr_r) || ((wop_rd_ptr_r[0] != wop_wr_ptr_r[0]) && lst_beat))
             ) begin
            //initialize command table and start issue
            npu_axi_state_en    = 1'b1;
            npu_axi_state_nxt   = npu_axi_status_issue_e;
            xm_w_accept         = 1'b1;
          end
        end
    endcase // casez (npu_axi_state_r)
  end : npu_axi_nxt_PROC

  // Pipe register
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : reg_pipe_PROC
    if (rst_dp == 1'b1)
    begin
      buffer_alloc_r       <= '0;        
      xm_cmd_r             <= '0;
      xm_err_r             <= 'b0;
      xm_boost_r           <= 'b0;
      npu_axi_state_r      <= npu_axi_status_idle_e;
      wlent_r              <= 'b0;
      wop_wr_ptr_r         <= 'b0;
      wop_rd_ptr_r         <= 'b0;
      wop_r                <= 'b0;

    end
    else begin
      if (buffer_alloc_en)
        buffer_alloc_r <= buffer_alloc_nxt;
      if (xm_cmd_en)
        xm_cmd_r <= xm_cmd_nxt;
      if (xm_err_en)
        xm_err_r <= xm_err_nxt;
      if (xm_boost_en)
        xm_boost_r <= xm_boost_nxt;
      if (npu_axi_state_en)
        npu_axi_state_r <= npu_axi_state_nxt;
      if (wlent_en)
        wlent_r <= wlent_nxt;
      if (wop_wr_ptr_en)
        wop_wr_ptr_r <= wop_wr_ptr_nxt;
      if (wop_rd_ptr_en)
        wop_rd_ptr_r <= wop_rd_ptr_nxt;
      for (int n = 0; n < AXI_OST; n++)
      begin
        if (wop_en[n])
          wop_r[n] <= wop_nxt[n];
      end
    end
  end : reg_pipe_PROC

// spyglass disable_block W287b
  // read response FIFO
  npu_fifo
    #(
      .SIZE   ( BFIFO_SIZE          ),
      .DWIDTH ( 1                   ),
      .FRCVAL ( 1'b0                ),
      .FRCACC ( 1'b0                )
      ) 
  u_bresp_inst
    (
     .clk          ( clk          ),
     .rst_a        ( rst_dp       ),
     .valid_write  ( b_push       ),
     .accept_write ( b_push_accept),
     .data_write   ( 1'b1         ),
     .valid_read   ( b_valid      ),
     .accept_read  ( b_pop        ),
     .data_read    (              )
     );
// spyglass enable_block W287b

  // Assigns
  assign idle     = ((npu_axi_state_r == npu_axi_status_idle_e) && (wop_rd_ptr_r == wop_wr_ptr_r) && (~b_valid));
  assign lst_beat = (wlent_r == wop_r[wop_rd_ptr_r[ENTRIES_WIDTH-1:0]].lent) ? 1'b1 : 1'b0;
  assign err_st   = xm_err_r;

endmodule : npu_ustu_axi_write
