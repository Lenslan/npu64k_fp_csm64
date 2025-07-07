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
// Top-level file for the oDMA VM LOAD
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"

module npu_idma_gather_idx_load
  import npu_types::*;
(
   input  logic            clk,      // clock
   input  logic            rst_a,    // asynchronous reset, active high
   // New descr issue
   input  logic            hlapi_i_valid,   // start new iteration
   output logic            hlapi_i_accept,  // acknowledge start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  hlapi_xm_agu_t   hlapi_i_seq,     // AGU params 
// spyglass enable_block W240
   input  logic            hlapi_i_gather,  // iDMA Gather load enable 

  // VM Request Interface
  `VMRMST(1,vm_rd_),                          // VM read
   // Gather VM load
   output gidx_t [1:0]     gather_idx,
   output logic            gather_valid,
   input  logic            gather_accept
);

  localparam int           N       = 3;
  localparam int           FIFO_SZ = 2;
  // Local parameters
  typedef enum logic [2:0] { 
    gidx_ld_status_idle_e,  // issue state is idle
    gidx_ld_status_issue_e  // issue the fm seq 
  } gidx_ld_state_t;

  logic                    vm_agu_init_req;
  logic                    vm_agu_init_ack;
  hlapi_vm_agu_t           vm_agu_params;
  vm_addr_t                vm_waddr;    // Generated VM address 
  logic                    vm_valid;    // Enable each VM lanes
  logic                    vm_accept;   // Accept by VM load/store
  logic                    vm_in_req;
  logic                    vm_in_ack;
  offset_t [N-1:0]         vm_in_shp;
  logic    [N-1:0]         vm_it_first;
  logic    [N-1:0]         vm_it_last;
  logic                    vm_it_vald;
  logic                    vm_it_req;
  logic                    vm_it_ack;
  logic                    vm_idle;

  gidx_ld_state_t          gidx_ld_state_r;
  gidx_ld_state_t          gidx_ld_state_nxt;
  logic                    gidx_ld_state_en;

  //command FIFO wires
  logic                    push_cmd;
  logic                    cmd_fifo_avail;

  logic [2:0]              idx_sel_r;
  logic [2:0]              idx_sel_nxt;
  logic                    idx_sel_en;

  logic [1:0]              idx_push_valid_r;
  logic [1:0]              idx_push_valid_nxt;
  logic                    idx_push_valid_en;

  ixpix_t  [1:0]           gather_pool_r;
  ixpix_t  [1:0]           gather_pool_nxt;
  logic                    gather_pool_en;

  //Data FIFO wires
  logic                    push_rd;
  logic [ISIZE*PIX_W-1:0]  rd_fifo_wdata;
  logic                    vld_rd;
  logic                    pop_rd;
  logic [ISIZE*PIX_W-1:0]  rd_fifo_rdata;

// spyglass disable_block W164a W486
//SMD:Width mismatch
//SJ :intentional shift
// spyglass enable_block W164a W486
  always_comb
  begin : gather_load_PROC // {
    idx_sel_nxt       = idx_sel_r;
    idx_sel_en        = 1'b0;
    vm_agu_init_req   = 1'b0;
    vm_agu_params     =  'b0;
    vm_accept         = 1'b0;

    push_cmd          = 1'b0;
    push_rd           = 1'b0;
    pop_rd            = 1'b0;
    rd_fifo_wdata     =  'b0;

    gather_pool_nxt   = gather_pool_r;
    gather_pool_en    = 1'b0;
    idx_push_valid_nxt= idx_push_valid_r;
    idx_push_valid_en = 1'b0;
    vm_rd_cmd_valid   = 1'b0;
    vm_rd_cmd_addr    =  'b0;
    gather_valid      = 1'b0;
    gather_idx        =   '0;

// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow
    // Execute command iteration
    if ((gidx_ld_state_r == gidx_ld_status_idle_e) && (hlapi_i_valid) && (hlapi_i_gather == 1'b1)) begin // {
      vm_agu_init_req       =   1'b1;
      vm_agu_params.ptr     =   hlapi_i_seq.p.g.gptr;
      vm_agu_params.buffer  =   hlapi_i_seq.b.g.gbuf;
      vm_agu_params.offsets =   {{(NUM_FM_LOOPS-N){16'd1}},hlapi_i_seq.o.g.goffsets};
      vm_agu_params.iter    =   {{(NUM_FM_LOOPS-N){16'd1}},16'd2,hlapi_i_seq.iter[N-2:0]};
      idx_sel_nxt           =    'b0;
      idx_sel_en            =   1'b1;
    end // }
    else if ((gidx_ld_state_r == gidx_ld_status_issue_e) && (cmd_fifo_avail)) begin // {
      vm_rd_cmd_valid       =  vm_valid;
      vm_rd_cmd_addr        =  vm_waddr;
      if (vm_rd_cmd_accept) begin
        push_cmd            =  1'b1;
        vm_accept           =  1'b1;
      end
    end // }
// spyglass enable_block W164a

    // Collect data
    if (vm_rd_rvalid) begin
      push_rd           =  1'b1;
      rd_fifo_wdata     =  vm_rd_rdata;
    end

    // Generate IDX
    if ((vld_rd) && (idx_push_valid_r != 2'b11)) begin
      idx_push_valid_nxt = {idx_push_valid_r[0],1'b1};
      gather_pool_nxt    = {rd_fifo_rdata,gather_pool_r[1]};
      idx_push_valid_en  = 1'b1;
      gather_pool_en     = 1'b1;
      pop_rd             = 1'b1;
    end
    if (idx_push_valid_r == 2'b11) begin
      gather_valid         = 1'b1;
      if (gather_accept) begin
        idx_sel_nxt        = idx_sel_r + 3'h1;
        idx_sel_en         = 1'b1;
        idx_push_valid_nxt = 2'b00;
        idx_push_valid_en  = (idx_sel_r == 3'h7) ? 1'b1 : 1'b0;
      end
    end

    gather_idx[0]        = (gather_pool_r[0] >> {idx_sel_r,4'h0}) & 16'hFFFF;
    gather_idx[1]        = (gather_pool_r[1] >> {idx_sel_r,4'h0}) & 16'hFFFF;

  end // }

  //
  // gidx_ld next state
  //
  // gidx_ld state
  // outputs: 
  always_comb
  begin : gidx_ld_nxt_PROC
    hlapi_i_accept      = 1'b0;
    gidx_ld_state_en    = 1'b0;
    gidx_ld_state_nxt   = gidx_ld_state_r;
    casez (gidx_ld_state_r)
      gidx_ld_status_issue_e:
        begin
          if (vm_idle) begin
            gidx_ld_state_en  = 1'b1;
            gidx_ld_state_nxt = gidx_ld_status_idle_e;
          end
        end
      default: // gidx_ld_status_idle_e
        begin
          // idle, wait for next request
          hlapi_i_accept   = vm_agu_init_ack;
          if (hlapi_i_valid & (hlapi_i_gather == 1'b1)) begin
            gidx_ld_state_en  = 1'b1;
            gidx_ld_state_nxt = gidx_ld_status_issue_e;
          end
        end
    endcase // casez (gidx_ld_state_r)
  end : gidx_ld_nxt_PROC

  //
  // FSM & Register
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_and_regisster_PROC
    if (rst_a == 1'b1)
    begin
      gidx_ld_state_r <= gidx_ld_status_idle_e;
      idx_sel_r       <= 'b0;
      idx_push_valid_r<= 'b0;
      gather_pool_r   <=  '0;
    end
    else
    begin
      if (gidx_ld_state_en)
      begin
        gidx_ld_state_r <= gidx_ld_state_nxt;
      end
      if (idx_sel_en)
      begin
        idx_sel_r       <= idx_sel_nxt;
      end
      if (idx_push_valid_en)
      begin
        idx_push_valid_r<= idx_push_valid_nxt;
      end
      if (gather_pool_en)
      begin
        gather_pool_r   <= gather_pool_nxt;
      end
    end
  end : fsm_and_regisster_PROC

// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentional open
  // FIFO to store command 
  npu_fifo 
  #(
    .SIZE   ( FIFO_SZ ),
    .DWIDTH ( 1  )
  )
  u_rcmd_fifo_inst
  (           
     .clk          ( clk                 ),
     .rst_a        ( rst_a               ),
     .valid_write  ( push_cmd            ), 
     .accept_write ( cmd_fifo_avail      ),
     .data_write   ( 1'b0                ),
     .valid_read   (                     ),
     .accept_read  ( pop_rd              ),
     .data_read    (                     )
  );

  // FIFO to store rdata
  
  npu_fifo 
  #(
    .SIZE   ( FIFO_SZ ),
    .DWIDTH (ISIZE*PIX_W)
  )
  u_rdata_fifo_inst
  (           
     .clk          ( clk                 ),
     .rst_a        ( rst_a               ),
     .valid_write  ( push_rd             ), 
     .accept_write (                     ),
     .data_write   ( rd_fifo_wdata       ),
     .valid_read   ( vld_rd              ),
     .accept_read  ( pop_rd              ),
     .data_read    ( rd_fifo_rdata       )
  );
// spyglass enable_block W287b

  npu_iterator
  #(
      .N (N),
      .S (1)
  ) u_npu_vm_iter (
    .clk           (clk                 ),
    .rst_a         (rst_a               ),
    .soft_rst      (1'b0                ),
    .in_req        (vm_in_req           ),
    .in_ack        (vm_in_ack           ),
    .in_shp        (vm_in_shp           ),
    .it_req        (vm_it_req           ),
    .it_ack        (vm_it_ack           ),
    .it_first      (vm_it_first         ),
    .it_last       (vm_it_last          ),
    .it_vald       (vm_it_vald          ) 
  );

  npu_dma_vm_agu
  #(
      .N (N),
      .S (1)
  ) u_npu_vm_agu (
    .clk           (clk                 ),
    .rst_a         (rst_a               ),
    // New descr issue
    .in_req        (vm_agu_init_req     ),
    .in_ack        (vm_agu_init_ack     ),
    .in_shp        (vm_agu_params       ),
    // Iterations
    .vm_in_req     (vm_in_req           ),
    .vm_in_ack     (vm_in_ack           ),
    .vm_in_shp     (vm_in_shp           ),
    .vm_it_req     (vm_it_req           ),
    .vm_it_ack     (vm_it_ack           ),
    .vm_it_first   (vm_it_first         ),
    .vm_it_last    (vm_it_last          ), 
    .vm_it_vald    (vm_it_vald          ),

    // VM sequence
    .vm_addr       (vm_waddr            ),
    .vm_valid      (vm_valid            ),
    .vm_accept     (vm_accept           ),

    // Idle
    .idle          (vm_idle             )
  );


endmodule : npu_idma_gather_idx_load
