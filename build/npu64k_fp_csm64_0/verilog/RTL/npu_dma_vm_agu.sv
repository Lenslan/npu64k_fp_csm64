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
// Top-level file for the DMA VM AGU
//
 
module npu_dma_vm_agu
  import npu_types::*;
  #(
      parameter int N = NUM_FM_LOOPS,    //  Iteration Nested Loop
      parameter int S = 4                //  Iteration step
  )
(
// spyglass disable_block W240
// SMD: Declare but not used 
// SJ: Not used signals 
   input  logic                   clk,      // clock
   input  logic                   rst_a,    // asynchronous reset, active high
   // New descr issue
   input  logic                   in_req,   // start new iteration
   output logic                   in_ack,   // acknowledge start
   input  hlapi_vm_agu_t          in_shp,   // shape of the iterator

   // Iterations
   output logic                   vm_in_req,   // start new iteration
   input  logic                   vm_in_ack,   // acknowledge start
   output offset_t        [N-1:0] vm_in_shp,   // shape of the iterator
   input  logic                   vm_it_req,   // iterator valid
   output logic                   vm_it_ack,   // iterator accept
   input  logic    [S-1:0][N-1:0] vm_it_first, // first bits
   input  logic    [S-1:0][N-1:0] vm_it_last,  // last bits
   input  logic    [S-1:0]        vm_it_vald,  // valid bits
// spyglass enable_block W240

   // VM data process interface 
   output vm_addr_t [S-1:0]       vm_addr,     // Generated VM address 
   output logic     [S-1:0]       vm_valid,    // Enable each VM lanes
   input  logic                   vm_accept,   // Accept by VM load/store

   //IDLE
   output logic                   idle
 );

  // Local parameters
  typedef enum logic [0:0] { 
    vm_agu_state_idle_e,  // issue state is idle
    vm_agu_state_issue_e  // issue the vm seq 
  } vm_agu_state_t;

  
  //
  // local functions
  //
  function automatic vm_addr_t vm_addr_wrap(
      input   vm_addr_t               vm_ptr,
      input   buf_t                   vm_buffer,
      input   logic    [S-1:0][N-1:0] vm_it_last,
      input   offset_t [N-1:0]        offsets,
      input   int                     idx
  );
    logic     f;
    offset_t  offs;
    offset_t  ad;

    offs = 0;
    for (int i = 0; i < idx; i++)
    begin
      f = 0;
      ad = 0;
      for (int n = N-1; n >= 0; n--)
      begin
        // sum offsets 
        if ((vm_it_last[i][n]  == 1'b0) & (~f)) 
        begin
          ad |= offsets[n];
          f  |= 1'b1;
        end
      end
      offs += ad;
    end  
    return incr_vm(vm_ptr, offs, vm_buffer);
  endfunction : vm_addr_wrap


  // Internal signals
  vm_agu_state_t           vm_agu_state_r;
  vm_agu_state_t           vm_agu_state_nxt;
  logic                    vm_agu_state_en;
  // burst ptr
  vm_addr_t                vm_ptr_r;
  vm_addr_t                vm_ptr_nxt;
  logic                    vm_ptr_en;
  // buffer ptr
  buf_t                    vm_buffer_r;
  buf_t                    vm_buffer_nxt;
  logic                    vm_buffer_en;
  // Offsets
  offset_t  [N-1:0]        vm_offsets_r;
  offset_t  [N-1:0]        vm_offsets_nxt;

  logic                    lst_issued;
  logic                    rd_valid;
  logic     [S-1:0]        rd_vm_valid;

  // Add internal buffer to optimization on timing
  vm_addr_t [S-1:0]        int_vm_addr;     // Generated VM address 
  logic                    int_vm_accept;   // Accept by VM load/store
  logic                    int_vm_push;     // Push to FIFO

  // Add slice_int to optimization on timing
  logic                    vm_it_req2;   // iterator valid
  logic                    vm_it_ack2;   // iterator accept
  logic     [S-1:0][N-1:0] vm_it_last2;  // last bits
  logic     [S-1:0]        vm_it_vald2;  // valid bits


// spyglass disable_block ReserveName
// SMD: Use Reserved Name
// SJ: Define in NPU TYPE 
  assign vm_buffer_nxt  = in_shp.buffer;
// spyglass enable_block ReserveName
  assign vm_buffer_en   = (vm_agu_state_r == vm_agu_state_idle_e) && in_req && vm_in_ack;
  assign vm_offsets_nxt = in_shp.offsets;
  assign vm_in_shp      = in_shp.iter;

  
  //
  // FSM outputs
  //
  always_comb
  begin : vm_agu_issue_PROC
    // default values
    vm_ptr_nxt       = '0;
    vm_ptr_en        = 1'b0;
    lst_issued       = 1'b0;
    int_vm_addr      =  'b0;
    vm_it_ack2       = 1'b0;
    int_vm_push      = 1'b0;

    // internal address
    for (int i = 0; i < S; i++) 
    begin
      int_vm_addr[i]  = vm_addr_wrap(vm_ptr_r, vm_buffer_r, vm_it_last2, vm_offsets_r, i);
    end
    
    // next pointer
    case (vm_agu_state_r)
    vm_agu_state_idle_e:
      begin
        vm_ptr_nxt      = in_shp.ptr;
      end
    default: // vm_agu_state_issue_e:
      begin
        for (int i = 0; i < S; i++) 
        begin
          lst_issued |= &vm_it_last2[i];
        end
        lst_issued &= vm_it_req2;
        vm_ptr_nxt  = vm_addr_wrap(vm_ptr_r, vm_buffer_r, vm_it_last2, vm_offsets_r, S);
      end
    endcase // case (vm_agu_state_r)

    // controls
    case (vm_agu_state_r)
    vm_agu_state_idle_e:
      begin
        vm_ptr_en = in_req & vm_in_ack;
      end
    default: // vm_agu_state_issue_e:
      begin
        int_vm_push = vm_it_req2;
        vm_it_ack2  = int_vm_accept;
        vm_ptr_en   = vm_it_req2 & int_vm_accept;
      end
    endcase // case (vm_agu_state_r)
  end : vm_agu_issue_PROC


  //
  // VM AGU next state
  //
  // VM AGU state 
  always_comb
  begin : vm_agu_nxt_PROC
    in_ack              = 1'b0;
    vm_in_req           = 1'b0;
    vm_agu_state_en     = 1'b0;
    vm_agu_state_nxt    = vm_agu_state_idle_e;
    casez (vm_agu_state_r)
      vm_agu_state_issue_e:
        begin
          vm_agu_state_nxt = vm_agu_state_idle_e;
          vm_agu_state_en  = lst_issued && int_vm_accept;
        end
    default: // vm_agu_state_idle_e
      begin
        // idle, wait for next request
          in_ack           = vm_in_ack;
          vm_in_req        = in_req;
          vm_agu_state_nxt = vm_agu_state_issue_e;
          vm_agu_state_en  = in_req && vm_in_ack;
        end
    endcase // casez (vm_agu_state_r)
  end : vm_agu_nxt_PROC


  //
  // FSM 
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_PROC
    if (rst_a == 1'b1)
    begin
      vm_agu_state_r <= vm_agu_state_idle_e;
    end
    else if (vm_agu_state_en)
    begin
      vm_agu_state_r <= vm_agu_state_nxt;
    end
  end : fsm_PROC
  

  //
  // Register assign
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_pipe_PROC
    if (rst_a == 1'b1)
    begin
      vm_ptr_r         <= 'b0;
      vm_buffer_r      <= '0;
      vm_offsets_r     <= 'b0;
    end
    else 
    begin
      if (vm_ptr_en)
      begin
        vm_ptr_r       <= vm_ptr_nxt;
      end
      if (vm_buffer_en)
      begin
        vm_buffer_r    <= vm_buffer_nxt;
        vm_offsets_r   <= vm_offsets_nxt;
      end
    end
  end : reg_pipe_PROC

  
  npu_fifo 
  #(
    .SIZE          ( 2    ),
    .DWIDTH        ( S*17 )
  )
  u_vm_addr_fifo_inst
  (           
     .clk          ( clk                       ),
     .rst_a        ( rst_a                     ),
     .valid_write  ( int_vm_push               ), 
     .accept_write ( int_vm_accept             ),
     .data_write   ( {vm_it_vald2,int_vm_addr} ),
     .valid_read   ( rd_valid                  ),
     .accept_read  ( vm_accept                 ),
     .data_read    ( {rd_vm_valid,vm_addr}     )
  );

  
  // register slice on iterator output
  npu_slice_int 
  #(
      .DWIDTH(N*S+S)
  ) 
  u_stu_r_chnl
   (.clk          (clk),
    .rst_a        (rst_a),
    .valid_write  (vm_it_req),
    .accept_write (vm_it_ack),
    .data_write   ({vm_it_last, vm_it_vald}),
    .valid_read   (vm_it_req2),
    .accept_read  (vm_it_ack2),
    .data_read    ({vm_it_last2, vm_it_vald2}) 
   );
  

  // Output Assign
  assign idle     = (vm_agu_state_r == vm_agu_state_idle_e) && (rd_valid == 1'b0);
  assign vm_valid = rd_valid ? rd_vm_valid : 'b0;

endmodule : npu_dma_vm_agu


