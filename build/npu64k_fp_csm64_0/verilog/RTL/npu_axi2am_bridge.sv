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

// This module is for split the transaction in one ID from master to multiple sigle burst transaction with one ID
//
 
`include "npu_defines.v"

`include "npu_axi_macros.svh"
`include "npu_am_macros.svh"

module npu_axi2am_bridge
  import npu_types::*;
  #(
  parameter D_WIDTH  = 64,
  parameter ID_WIDTH = 1,
  parameter MEM_AW   = 17,
  parameter RD_OSD   = 8,
  parameter WR_OSD   = 8
  )
  (

// spyglass disable_block W240
// SMD:Unread input
// SJ :Ignore axi macro, some of signals will not be used 
   `AXISLV(ID_WIDTH,D_WIDTH,1,1,1,1,1,axi_slv_),
// spyglass enable_block W240

   // axi2am write request
   `AMWMST_MSK(nn_am_wr_,1),
   // axi2am read request
   `AMRMST(nn_am_rd_,1),
   
   
  input  logic                  rst_a,
  input  logic                  clk

);


localparam IDLE    = 1'b0;   // idle state,  when ar or aw request accepted, request for clock
localparam SPLIT   = 1'b1;   // split state, when splited num hit length, switch to idle
localparam AXI_LSB_ADDR = (`NPU_SLICE_MAC == 4096) ? 9 : 7;
localparam FIFO_DWIDTH = (`NPU_SLICE_MAC == 4096) ? 6 : 4;
localparam AM_SIZE = (`NPU_SLICE_MAC == 4096) ? 4096 : 1024;
localparam AM_STRB = 2*AM_SIZE/64;
localparam AM_DATA_W = VSIZE*ISIZE;
localparam AM_INDEX = AM_SIZE/64;

  logic                       waxi_state_r;
  logic                       waxi_state_nxt;
  logic                       waxi_state_en;

  logic                       raxi_state_r;
  logic                       raxi_state_nxt;
  logic                       raxi_state_en;

  logic                       waxi_done;
  logic                       raxi_done;

  logic  [39:0]               axi_awaddr_r;
  logic  [39:0]               axi_awaddr_nxt;
  logic                       axi_awaddr_en;

  logic  [ID_WIDTH-1:0]       axi_awid_r;
  logic                       axi_awuser_r;
  logic  [2:0]                axi_awsize_r;
  logic                       axi_aw_en;

  logic  [39:0]               axi_araddr_r;
  logic  [39:0]               axi_araddr_nxt;
  logic                       axi_araddr_en;

  logic  [ID_WIDTH-1:0]       axi_arid_r;
  logic                       axi_aruser_r;
  logic  [3:0]                axi_arlen_r;
  logic  [2:0]                axi_arsize_r;
  logic                       axi_ar_en;
  logic                       axi_rlast;

  logic  [3:0]                rbrst_cntr_r;
  logic  [3:0]                rbrst_cntr_nxt;
  logic                       rbrst_cntr_en;

  // BRESP FIFO
  logic                       buser;
  logic  [ID_WIDTH-1:0]       bid;

  logic                       br_fifo_accept_write;
  logic                       br_fifo_valid_write;
  logic                       br_fifo_valid_read;
  logic                       br_fifo_accept_read;
  
  // READ FIFO to have ID trace and rlast gen
  logic                       ruser;
  logic                       rlast;
  logic  [ID_WIDTH-1:0]       rid;
  logic  [FIFO_DWIDTH-1:0]    rd_bank_sel;
  logic  [D_WIDTH-1:0]        rdata_push;
  logic  [AM_SIZE-1:0]        rd_data_plane;
  logic  [AM_STRB-1:0]        wr_strb_plane;

  logic                       ar_fifo_vld_write_m;
  logic                       ar_fifo_accept_write;
  logic                       ar_fifo_valid_write;
  logic                       ar_fifo_valid_read;
  logic                       ar_fifo_accept_read;
  logic                       arshw_fifo_accept_read;
  
  logic                       rd_fifo_valid_write;
  logic                       rd_fifo_valid_read;
  logic                       rd_fifo_accept_read;



// Write Channel
  always_comb
  begin: axi_write_PROC

    axi_awaddr_nxt  = axi_awaddr_r + (1'b1 << axi_awsize_r);
    axi_awaddr_en   = 1'b0;
    axi_aw_en       = 1'b0;

    // Flags
    waxi_done       = 1'b0;

    case (waxi_state_r)
      IDLE: begin
        if (axi_slv_awvalid && br_fifo_accept_write) begin
          // Buffer Information
          axi_awaddr_nxt  = axi_slv_aw.addr ;
          axi_awaddr_en   = 1'b1;
          axi_aw_en       = 1'b1;
        end
      end
      SPLIT: begin
        begin
          if (axi_slv_wvalid && nn_am_wr_cmd_accept) begin
            axi_awaddr_en  = 1'b1;
            if (axi_slv_wlast) begin
              waxi_done       = 1'b1;
            end
          end
        end
      end
    endcase
  end : axi_write_PROC

// Read Channel
  always_comb
  begin: axi_read_PROC

    axi_araddr_en   = 1'b0;
    axi_araddr_nxt  = axi_araddr_r + (1'b1 << axi_arsize_r);
    axi_ar_en       = 1'b0;
    axi_rlast       = 1'b0;

    rbrst_cntr_nxt  = rbrst_cntr_r + 4'b1;
    rbrst_cntr_en   = 1'b0;

    // Flags
    raxi_done       = 1'b0;

    case (raxi_state_r)
      IDLE: begin
        if (axi_slv_arvalid && ar_fifo_accept_write) begin
          // Buffer Information
          axi_araddr_nxt  = axi_slv_ar.addr;
          axi_araddr_en   = 1'b1;
          axi_ar_en       = 1'b1;
        end
      end
      SPLIT: begin
        if (ar_fifo_accept_write && nn_am_rd_cmd_accept) begin
          axi_araddr_en   = 1'b1;
          rbrst_cntr_en   = 1'b1;
          if (rbrst_cntr_r == axi_arlen_r) begin
            rbrst_cntr_nxt = 4'b0;
            raxi_done      = 1'b1;
            axi_rlast      = 1'b1;
          end
        end
      end
    endcase
  end: axi_read_PROC

  // FSM
  assign   waxi_state_nxt  =  (waxi_state_r == IDLE) ? ((axi_slv_awvalid && br_fifo_accept_write) ? SPLIT : IDLE)
                                                     : (waxi_done ? IDLE : SPLIT);
  assign   raxi_state_nxt  =  (raxi_state_r == IDLE) ? ((axi_slv_arvalid && ar_fifo_accept_write) ? SPLIT : IDLE)
                                                     : (raxi_done ? IDLE : SPLIT);
  always @(posedge clk or posedge rst_a)
  begin: fsm_nxt_PROC
    if (rst_a == 1'b1) begin
      waxi_state_r  <=  IDLE;
      raxi_state_r  <=  IDLE;
    end
    else begin
      waxi_state_r  <=  waxi_state_nxt;
      raxi_state_r  <=  raxi_state_nxt;
    end
  end
  
  // 
  // Register
  always @(posedge clk or posedge rst_a)
  begin: Register_Pipe_PROC
    if (rst_a == 1'b1) begin
      axi_awaddr_r   <= 'b0;
      axi_awid_r     <= 'b0;
      axi_awuser_r   <= 'b0;
      axi_awsize_r   <= 'b0;
      axi_araddr_r   <= 'b0;
      axi_arid_r     <= 'b0;
      axi_aruser_r   <= 'b0;
      axi_arlen_r    <= 'b0;
      axi_arsize_r   <= 'b0;
      rbrst_cntr_r   <= 'b0;
    end
    else begin
      if (axi_awaddr_en) begin
        axi_awaddr_r   <= axi_awaddr_nxt;
      end
      if (axi_aw_en) begin
        axi_awid_r     <= axi_slv_awid;
        axi_awuser_r   <= axi_slv_awuser;
        axi_awsize_r   <= axi_slv_aw.size;
      end
      if (axi_araddr_en) begin
        axi_araddr_r   <= axi_araddr_nxt ;
      end
      if (axi_ar_en) begin
        axi_arid_r     <= axi_slv_arid;
        axi_aruser_r   <= axi_slv_aruser;
        axi_arlen_r    <= axi_slv_ar.len;
        axi_arsize_r   <= axi_slv_ar.size;
      end
      if (rbrst_cntr_en) begin
        rbrst_cntr_r   <= rbrst_cntr_nxt ;
      end
    end
  end
  // 
// spyglass disable_block W287b
// SMD: disconnect signal 
// SJ: Intended open 
  npu_fifo #(
            .SIZE    (WR_OSD),
            .DWIDTH  (ID_WIDTH+1)
  ) u_bresp_fifo_inst(
    .clk          ( clk                  ),
    .rst_a        ( rst_a                ),
    .valid_write  ( br_fifo_valid_write  ),
    .accept_write ( br_fifo_accept_write ),
    .data_write   ( {axi_awid_r,axi_awuser_r}),
    .valid_read   ( br_fifo_valid_read   ),
    .accept_read  ( br_fifo_accept_read  ),
    .data_read    ( {bid,buser}          )
    );
  
  
  npu_fifo #(
            .SIZE    (RD_OSD),
            .FRCACC  (1),
            .FRCVAL  (1),
            .DWIDTH  (FIFO_DWIDTH)
  ) u_ar_fifo_inst(
    .clk          ( clk                          ),
    .rst_a        ( rst_a                        ),
    .valid_write  ( ar_fifo_vld_write_m          ),
    .accept_write (                              ),
    .data_write   ( axi_araddr_r[AXI_LSB_ADDR-1:3]),
    .valid_read   (                              ),
    .accept_read  ( ar_fifo_accept_read          ),
    .data_read    ( rd_bank_sel                  )
    );

  npu_fifo #(
            .SIZE    (RD_OSD),
            .DWIDTH  (ID_WIDTH+1+1)
  ) u_ar_shadow_fifo_inst(
    .clk          ( clk                          ),
    .rst_a        ( rst_a                        ),
    .valid_write  ( ar_fifo_valid_write          ),
    .accept_write ( ar_fifo_accept_write         ),
    .data_write   ( {axi_arid_r,axi_aruser_r,axi_rlast}),
    .valid_read   (                              ),
    .accept_read  ( arshw_fifo_accept_read       ),
    .data_read    ( {rid,ruser,rlast})
    );

  npu_fifo #(
            .SIZE    (RD_OSD),
            .FRCACC  (1),
            .DWIDTH  (D_WIDTH)
  ) u_rd_fifo_inst(
    .clk          ( clk                          ),
    .rst_a        ( rst_a                        ),
    .valid_write  ( rd_fifo_valid_write          ),
    .accept_write (                              ),
    .data_write   ( rdata_push                   ),
    .valid_read   ( rd_fifo_valid_read           ),
    .accept_read  ( rd_fifo_accept_read          ),
    .data_read    ( axi_slv_rdata                )
    );

// spyglass enable_block W287b
  
  // Internal Wires
  assign  br_fifo_valid_write    = axi_slv_wvalid && axi_slv_wready & axi_slv_wlast;
  assign  br_fifo_accept_read    = axi_slv_bready;
  assign  ar_fifo_vld_write_m    = (raxi_state_r == SPLIT) && nn_am_rd_cmd_accept && ar_fifo_accept_write;
  assign  ar_fifo_valid_write    = (raxi_state_r == SPLIT) && nn_am_rd_cmd_accept;
  assign  ar_fifo_accept_read    = nn_am_rd_rvalid;
  assign  arshw_fifo_accept_read = axi_slv_rvalid && axi_slv_rready;
  assign  rd_fifo_valid_write    = nn_am_rd_rvalid;
  assign  rd_fifo_accept_read    = axi_slv_rready;
  
  // AXI write Channel
  assign  nn_am_wr_cmd_valid  = (waxi_state_r == SPLIT) && axi_slv_wvalid;
// spyglass disable_block W164b
//SMD:LHS larger than RHS
//SJ :RHS is the real memory while LHS is MAX size, in sram will be trunk
  assign  nn_am_wr_cmd_addr   = axi_awaddr_r[MEM_AW-1:AXI_LSB_ADDR];
// spyglass enable_block W164b
  assign  nn_am_wr_wdata      = {AM_INDEX{axi_slv_wdata}};
  assign  nn_am_wr_wstrb      = wr_strb_plane;
  
// spyglass disable_block W362 SelfDeterminedExpr-ML
//SMD:Width mismatch
//SJ :No overflow
  // derive strobe
  always_comb
  begin : wstrb_PROC
    wr_strb_plane = '0;
    for (int i = 0; i< AM_INDEX; i++) 
    begin
      if (axi_awaddr_r[AXI_LSB_ADDR-1:3] == unsigned'(i)) 
      begin 
        wr_strb_plane[i*2+:2]   = {|axi_slv_wstrb[7:4],|axi_slv_wstrb[3:0]};
      end
    end
  end : wstrb_PROC
// spyglass enable_block W362 SelfDeterminedExpr-ML

  assign  axi_slv_awready  =  (waxi_state_r == IDLE)  && br_fifo_accept_write;
  assign  axi_slv_wready   =  (waxi_state_r == SPLIT) && nn_am_wr_cmd_accept;
  assign  axi_slv_buser    =  buser;
  assign  axi_slv_bvalid   =  br_fifo_valid_read;
  assign  axi_slv_bid      =  bid;
  assign  axi_slv_bresp    =  npu_axi_resp_okay_e;

  // AXI read Channel
  assign  nn_am_rd_cmd_valid  = (raxi_state_r == SPLIT) && ar_fifo_accept_write;
// spyglass disable_block W164b
//SMD:LHS larger than RHS
//SJ :RHS is the real memory while LHS is MAX size, in sram will be trunk
  assign  nn_am_rd_cmd_addr   = axi_araddr_r[MEM_AW-1:AXI_LSB_ADDR];
// spyglass enable_block W164b
  assign  rd_data_plane       = nn_am_rd_rdata;

// spyglass disable_block W362 SelfDeterminedExpr-ML
//SMD:Width mismatch
//SJ :No overflow
  // select read data
  always_comb
  begin : rd_PROC
    rdata_push = '0;
    for (int n = 0; n<AM_INDEX; n++) 
    begin
      if (rd_bank_sel == unsigned'(n)) 
      begin
        rdata_push |= rd_data_plane[n*64+:64];
      end
    end
  end : rd_PROC
// spyglass enable_block W362 SelfDeterminedExpr-ML

  assign  axi_slv_arready  =  (raxi_state_r == IDLE) & ar_fifo_accept_write;
  assign  axi_slv_rvalid   =  rd_fifo_valid_read;
  assign  axi_slv_ruser    =  ruser;
  assign  axi_slv_rid      =  rid;
  assign  axi_slv_rresp    =  npu_axi_resp_okay_e;
  assign  axi_slv_rlast    =  rlast;

endmodule : npu_axi2am_bridge
