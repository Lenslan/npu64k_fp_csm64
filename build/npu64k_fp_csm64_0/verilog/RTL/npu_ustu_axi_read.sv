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
// Top-level file for the AXI read (single ID)
//

`include "npu_axi_macros.svh"

module npu_ustu_axi_read
  import npu_types::*;
  #(
    // AXI data with XM
    parameter AXI_MST_IDW = 4,
    parameter MAXIAWUW = 1,             // AXI MMIO slave AW user width
    parameter MAXIWUW  = 1,             // AXI MMIO slave W user width
    parameter MAXIBUW  = 1,             // AXI MMIO slave B user width
    parameter MAXIARUW = 1,             // AXI MMIO slave AR user width
    parameter MAXIRUW  = 1,             // AXI MMIO slave R user width
    parameter DATA_LEN = 6,
    parameter AXI_OST  = 16,
    parameter STU_D    = 512,
    parameter BUFFER_SIZE = 1024
   )
  (
   // interfaces
   //
// spyglass disable_block W240
//SMD:Unread input
//SJ :axi_rid and ruser signal are not used and ignore
   `AXIRMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,dma_saxi_),  // AXI data transfer, read-only
// spyglass enable_block W240
   // XM read request
   input  logic                    xm_r_valid,
   input  xm_buf_t                 xm_r_request,    // xm_len_t len: [31:0]; xm_ptr_t base: [ASIE-1:0];
   output logic                    xm_r_accept,
   input  logic                    boost,
   input  logic  [1:0]             ost_cfg,
   
   output logic                    buffer_wr_valid, 
   output logic  [5:0]             buffer_wr_num, 
   output logic  [5:0]             buffer_wr_alsb, 
   output logic  [511:0]           buffer_wr_data, 
   input  logic                    buffer_wr_accept,

   input  logic                    buffer_rls_valid,
   input  logic  [5:0]             buffer_rls,
   input  logic [64-1: 0]     vmid,
   output logic                    idle,            //AXI read is idle
   output logic                    err_st,          //AXI read got error response

   // clock and reset
   //
   input  logic                    clk,                    // clock, all logic clocked at posedge
   input  logic                    rst_dp                  // asynchronous reset, active high
  );

  // Parameters
  localparam int AXI_ALSB      = $clog2(STU_D/8);
  localparam int FUL_BSIZE     = STU_D*2;
  localparam int MAX_BSIZE     = BUFFER_SIZE/4;
  localparam int FUL_RLEN      = $clog2(FUL_BSIZE*8/STU_D);
  localparam int AXI_RLEN      = $clog2(MAX_BSIZE*8/STU_D);
  localparam int PTT_WIDTH     = $clog2(AXI_OST);
  localparam int CMD_SZ        = $bits(axi_cmd_t);
  localparam int LENT_MSB      = $clog2(FUL_BSIZE);

  typedef struct packed {
    logic [8:0]                    shamt;      //burst shift
    logic [8:0]                    lst_len;    //last beat len
    logic                          fstr;       //first trans flag
    logic [LENT_MSB:0]             lent;       //Reserve Buffer Length (MAX to 1024Bytes)
  } ptt_cmd_t;

  typedef ptt_cmd_t  [AXI_OST-1:0]   ptt_t;

// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow
  function automatic void xm_cmd_gen(input xm_buf_t xm_cmd_in, input logic boost, output axi_cmd_t xm_cmd_out);
    xm_len_t             len_t;
    xm_len_t             arlenb;
    logic [AXI_ALSB-1:0] pad_msk;
    logic [ASIZE-1:0]    addr_msk;
    logic [ASIZE-1:0]    len_msk;

    // address aligned to Data_Size
    addr_msk        =  ~((1<<AXI_ALSB) - 1);
    len_msk         =   ( 1<<AXI_ALSB) - 1 ;
    pad_msk         =   ( 1<<AXI_ALSB) - 1 ;
    arlenb          =   '0;

    // split transfer with STU_D*2 Bytes Boundary
    // Proposed maximum burst arlen
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Has default value, and RHS is the real size
    if (FUL_RLEN > AXI_RLEN) begin
      arlenb  =  boost ? {(~xm_cmd_in.base[AXI_ALSB+:FUL_RLEN]),pad_msk} : {(~xm_cmd_in.base[AXI_ALSB+:AXI_RLEN]),pad_msk};
    end
    else begin
      arlenb  =  {(~xm_cmd_in.base[AXI_ALSB+:AXI_RLEN]),pad_msk};
    end
// spyglass enable_block W164b

    // HW total length from aligned 512b addr
    len_t = xm_cmd_in.len + (xm_cmd_in.base & len_msk) - 1;

    if (arlenb < len_t) begin
      xm_cmd_out.xm_bcmd.len  = arlenb;
      xm_cmd_out.xm_bcmd.padm = 0;
      xm_cmd_out.xm_bcmd.base = (xm_cmd_in.base & addr_msk);
      xm_cmd_out.xm_ncmd.len  = len_t - arlenb;
      xm_cmd_out.xm_ncmd.padm = 0;
      xm_cmd_out.xm_ncmd.base = (xm_cmd_in.base & addr_msk) + arlenb + 1;
      xm_cmd_out.shamt        = (xm_cmd_in.base & len_msk);
      xm_cmd_out.lst          = 1'b0;
      xm_cmd_out.lst_len      = (arlenb == 32'd63) ? (9'd63 - (xm_cmd_in.base & len_msk)) : 9'd63;
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

  // PTT
  ptt_t                            ptt_r;
  ptt_t                            ptt_nxt;
  logic [AXI_OST-1:0]              ptt_en;

  logic [PTT_WIDTH:0]              ptt_head_r;
  logic [PTT_WIDTH:0]              ptt_head_nxt;
  logic                            ptt_head_en;

  logic [PTT_WIDTH:0]              ptt_tail_r;
  logic [PTT_WIDTH:0]              ptt_tail_nxt;
  logic                            ptt_tail_en;

  // Registers
  npu_axi_state_t                  npu_axi_state_r;
  npu_axi_state_t                  npu_axi_state_nxt;
  logic                            npu_axi_state_en;

  axi_cmd_t                        xm_cmd_r;
  axi_cmd_t                        xm_cmd_nxt;
  logic                            xm_cmd_en;

  logic                            xm_boost_r;
  logic                            xm_boost_nxt;
  logic                            xm_boost_en;

  logic                            xm_err_r;
  logic                            xm_err_nxt;
  logic                            xm_err_en;

  logic                            lst_issued;
  logic [PTT_WIDTH:0]              ptt_full;
  logic [PTT_WIDTH:0]              ptt_mask;

  // Connect to register Slice
  logic                            dma_saxi_rvalid2;
  logic                            dma_saxi_rready2;
  logic [STU_D-1:0]                dma_saxi_rdata2;
  logic                            dma_saxi_rlast2;
  npu_axi_resp_t                   dma_saxi_rresp2;

  logic [15:0]                     buffer_free_r;
  logic [15:0]                     buffer_free_nxt;
  logic                            buffer_free_en;

                           
// spyglass disable_block W164a
// SMD: LHS width is less than RHS
// SJ: Reviewed
  // Command & Package Update
  always_comb
  begin : dma_ptt_axi_PROC
    xm_cmd_en           = 1'b0;
    xm_cmd_nxt          = xm_cmd_r;
    xm_err_en           = 1'b0;
    xm_err_nxt          = xm_err_r;
    xm_boost_en         = 1'b0;
    xm_boost_nxt        = xm_boost_r;
    lst_issued          = 1'b0;
    dma_saxi_arvalid    = 1'b0;
    dma_saxi_rready2    = buffer_wr_accept;
    dma_saxi_arid       = 'b0;
    dma_saxi_aruser     = '0;
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Has default value, and STU doesn't has BDMA field
    dma_saxi_aruser     = vmid;
// spyglass enable_block W164b
    dma_saxi_ar.addr    = '0;
    dma_saxi_ar.cache   = 4'b0010;   // modifiable non-bufferable
    dma_saxi_ar.prot    = 3'b010; // unprivileged, non-secure, data access
    dma_saxi_ar.lock    = npu_axi_lock_normal_e;
    dma_saxi_ar.burst   = npu_axi_burst_incr_e;
    dma_saxi_ar.len     = 8'h00;
    dma_saxi_ar.size    = 3'd6;   // 512b data
    dma_saxi_ar.region  = '0;
    ptt_tail_en         = 1'b0;
    ptt_tail_nxt        = ptt_tail_r;
    ptt_head_en         = 1'b0;
    ptt_head_nxt        = ptt_head_r;
    ptt_en              = {AXI_OST{1'b0}};
    ptt_nxt             = ptt_r;
    buffer_wr_valid     = 1'b0;
    buffer_wr_alsb      = 'b0;
    buffer_wr_num       = 'b0;
    buffer_wr_data      = 'b0;
    buffer_free_nxt     = buffer_free_r;
    buffer_free_en      = 'b0;
    ptt_mask            = '0;
    ptt_full            = '0;

    case (ost_cfg)
      2'b01:
        begin
          ptt_full = {2'b1, {(PTT_WIDTH-1){1'b0}}};
          ptt_mask = {1'b0, {(PTT_WIDTH  ){1'b1}}};
        end // up to 50% AXI_OST -> 16
      2'b10:
        begin
          ptt_full = {3'b1, {(PTT_WIDTH-2){1'b0}}};
          ptt_mask = {2'b0, {(PTT_WIDTH-1){1'b1}}};
        end // up to 25% AXI_OST -> 8
      2'b11:
        begin
          ptt_full = {4'b1, {(PTT_WIDTH-3){1'b0}}};
          ptt_mask = {3'b0, {(PTT_WIDTH-2){1'b1}}};
        end // up to 12.5% AXI_OST -> 4
      default:
        begin
          ptt_full = {1'b1, {PTT_WIDTH{1'b0}}};
          ptt_mask = {      {(PTT_WIDTH+1){1'b1}}};
        end // up to AXI_OST -> 32
    endcase

    // Initialize issue
    if ((npu_axi_state_r == npu_axi_status_idle_e) && (xm_r_valid)) begin
      // Initialize burst command
      xm_cmd_en              =   1'b1;
      xm_cmd_gen(xm_r_request, boost, xm_cmd_nxt);
      // Lock Boost Mode
      xm_boost_nxt           =   boost;
      xm_boost_en            =   1'b1;
    end
    if (npu_axi_state_r == npu_axi_status_issue_e)begin
// spyglass disable_block SelfDeterminedExpr-ML W362
//SMD:Expression width mismatch (>=)
//SJ :Ignore buffer_free_r width mismatch with xm_cmd_r.xm_bcmd.len, no influence on function
      if ((((ptt_tail_r ^ ptt_head_r) & ptt_mask) != ptt_full) && // PTT not full
          (xm_boost_r || (buffer_free_r > (xm_cmd_r.xm_bcmd.len - xm_cmd_r.shamt))) // Buffer available check (Skip in boost mode)
         )
// spyglass enable_block SelfDeterminedExpr-ML W362
      begin 
        dma_saxi_arvalid  = 1'b1;
        dma_saxi_ar.addr  = xm_cmd_r.xm_bcmd.base;
        dma_saxi_ar.len   = xm_cmd_r.xm_bcmd.len[31:AXI_ALSB];
        if (dma_saxi_arready == 1'b1) begin
          // Push command to PTT
          ptt_tail_en                 = 1'b1;
          ptt_tail_nxt                = ptt_tail_r + 1;
          ptt_en[ptt_tail_r[PTT_WIDTH-1:0]]          = 1'b1;
          ptt_nxt[ptt_tail_r[PTT_WIDTH-1:0]].shamt   = xm_cmd_r.shamt;
          ptt_nxt[ptt_tail_r[PTT_WIDTH-1:0]].lst_len = xm_cmd_r.lst_len;
          ptt_nxt[ptt_tail_r[PTT_WIDTH-1:0]].fstr    = 1'b1;
          ptt_nxt[ptt_tail_r[PTT_WIDTH-1:0]].lent    = xm_cmd_r.xm_bcmd.len;

          // Update Command
          xm_cmd_en           = 1'b1;
          xm_cmd_gen(xm_cmd_r.xm_ncmd, xm_boost_r, xm_cmd_nxt);
          lst_issued          = (xm_cmd_r.lst == 1'b1);
// spyglass disable_block W116
//SMD:Expression width mismatch (-)
//SJ :Ignore buffer_free_r width mismatch with xm_cmd_r.xm_bcmd.len, no overflow
          buffer_free_nxt     = buffer_free_nxt - xm_cmd_r.xm_bcmd.len - 1 + xm_cmd_r.shamt;
// spyglass enable_block W116
          buffer_free_en      = 'b1;
        end
      end
    end

    // rdata return
    if (dma_saxi_rvalid2) begin
      xm_err_en            = 1'b1;
      xm_err_nxt           = (dma_saxi_rresp2 != npu_axi_resp_okay_e) && (dma_saxi_rresp2 != npu_axi_resp_exokay_e);
      buffer_wr_valid  = 1'b1;
      buffer_wr_data   = dma_saxi_rdata2;
      // First use shamt as lsb
      if (ptt_r[ptt_head_r[PTT_WIDTH-1:0]].fstr) begin
        buffer_wr_alsb   = ptt_r[ptt_head_r[PTT_WIDTH-1:0]].shamt;
        buffer_wr_num    = dma_saxi_rlast2 ?  ptt_r[ptt_head_r[PTT_WIDTH-1:0]].lst_len : (9'd63 - ptt_r[ptt_head_r[PTT_WIDTH-1:0]].shamt);
      end
      // Otherwise use 0 as lsb
      else begin
        buffer_wr_alsb   = 0;
        buffer_wr_num    = dma_saxi_rlast2 ?  ptt_r[ptt_head_r[PTT_WIDTH-1:0]].lst_len : 9'd63;
      end

      if (buffer_wr_accept) begin
        ptt_en[ptt_head_r[PTT_WIDTH-1:0]] = 1'b1;
        ptt_nxt[ptt_head_r[PTT_WIDTH-1:0]].fstr = 1'b0;
        if (dma_saxi_rlast2) begin
          // Release PTT when last accept
          ptt_head_en        = 1'b1;
          ptt_head_nxt       = ptt_head_r + 1;
        end
      end
    end

    if (xm_err_r == 1'b1) begin
      xm_err_en                 = 1'b1;
      xm_err_nxt                = 1'b0;
    end

// spyglass disable_block W116
//SMD:Expression width mismatch (-)
//SJ :Ignore buffer_free_r width mismatch with xm_cmd_r.xm_bcmd.len, no overflow
    if (buffer_rls_valid) begin
      buffer_free_nxt      = buffer_free_nxt + buffer_rls + 1;
      buffer_free_en       = 1'b1;
    end
// spyglass enable_block W116
  end : dma_ptt_axi_PROC
// spyglass enable_block W164a

  //
  // AXI read next state
  //
  always_comb
  begin : npu_axi_nxt_PROC
    npu_axi_state_en  = 1'b0;
    npu_axi_state_nxt = npu_axi_state_r;
    xm_r_accept       = 1'b0;
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
          if (xm_r_valid) begin
            //initialize command table and start issue
            npu_axi_state_en    = 1'b1;
            npu_axi_state_nxt   = npu_axi_status_issue_e;
            xm_r_accept       = 1'b1;
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
      buffer_free_r     <= BUFFER_SIZE;        
      xm_cmd_r          <= {CMD_SZ{1'b0}};
      xm_err_r          <= 'b0;
      xm_boost_r        <= 'b0;
      npu_axi_state_r   <= npu_axi_status_idle_e;

      ptt_r             <= 'b0;
      ptt_head_r        <= 'b0;
      ptt_tail_r        <= 'b0;

    end
    else begin
      if (buffer_free_en)
        buffer_free_r <= buffer_free_nxt;
      if (xm_cmd_en)
        xm_cmd_r <= xm_cmd_nxt;
      if (xm_err_en)
        xm_err_r <= xm_err_nxt;
      if (xm_boost_en)
        xm_boost_r <= xm_boost_nxt;
      if (npu_axi_state_en)
        npu_axi_state_r <= npu_axi_state_nxt;

      if (ptt_head_en)
        ptt_head_r <= ptt_head_nxt;
      if (ptt_tail_en)
        ptt_tail_r <= ptt_tail_nxt;
      for (int n = 0; n < AXI_OST; n++)
      begin
        if (ptt_en[n]) begin
          ptt_r[n] <= ptt_nxt[n];
        end
      end
    end
  end : reg_pipe_PROC

  // Assign output driver
  assign idle    = ((npu_axi_state_r == npu_axi_status_idle_e) && (ptt_tail_r == ptt_head_r));
  assign err_st  = xm_err_r;

npu_slice_int #(
    .DWIDTH(STU_D+3)
) u_stu_r_chnl
 (.clk          (clk),
  .rst_a        (rst_dp),
  .valid_write  (dma_saxi_rvalid),
  .accept_write (dma_saxi_rready),
  .data_write   ({dma_saxi_rdata, dma_saxi_rlast, dma_saxi_rresp}),
  .valid_read   (dma_saxi_rvalid2),
  .accept_read  (dma_saxi_rready2),
  .data_read    ({dma_saxi_rdata2, dma_saxi_rlast2, dma_saxi_rresp2}) 
 );

endmodule : npu_ustu_axi_read
