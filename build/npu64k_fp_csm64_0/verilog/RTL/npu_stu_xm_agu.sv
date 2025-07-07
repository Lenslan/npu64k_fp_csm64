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
// Top-level file for the XM AGU
//

module npu_stu_xm_agu
  import npu_types::*;
(
   input  logic            clk,      // clock
   input  logic            rst_a,    // asynchronous reset, active high
// spyglass disable_block W240
// SMD: Declare but Not used 
// SJ: Ignore 
   // New descr issue
   input  logic            hlapi_i_valid,  // start new iteration
   output logic            hlapi_i_accept,  // acknowledge start
   input  hlapi_stu_agu_t  hlapi_i_seq,  // AGU params 

   // Iterations
   output logic            xm_in_req,   // start new iteration
   input  logic            xm_in_ack,   // acknowledge start
   output offset_t [5:0]   xm_in_shp,   // shape of the iterator
   input  logic            xm_it_req,   // iterator valid
   output logic            xm_it_ack,   // iterator accept
   input  logic    [5:0]   xm_it_first, // first bits
   input  logic    [5:0]   xm_it_last,  // last bits
// spyglass enable_block W240

   // xm status
   output logic [31:0]     xm_len_trans,
   // xm request
   output logic            xm_valid,
   output xm_buf_t         xm_request,
   input  logic            xm_accept,
   output logic            boost,
   output logic [1:0]      ost_cfg,

   //IDLE
   output logic            idle
);

  // Local parameters
  typedef enum logic [2:0] { 
    xm_agu_state_idle_e,  // issue state is idle
    xm_agu_state_cal_e,   // calculation ful burst & alternative iteration
    xm_agu_state_req_e,   // request iteration 
    xm_agu_state_gen_e,   // generate xm command seq 
    xm_agu_state_issue_e  // issue the xm seq 
  } xm_agu_state_t;

  // Internal signals
  xm_agu_state_t           xm_agu_state_r;
  xm_agu_state_t           xm_agu_state_nxt;
  logic                    xm_agu_state_en;

  // Iteration Check Flag
  logic    [2:0]           xm_it_check_r;
  logic    [2:0]           xm_it_check_nxt;
  logic                    cont_r;
  logic                    cont_nxt;
  logic                    xm_it_check_en;

  // burst ptr
  xm_ptr_t                 xm_ptr_r;
  xm_ptr_t                 xm_ptr_nxt;
  logic                    xm_ptr_en;

  // buffer ptr
  xm_buf_t                 xm_buffer_r;
  xm_buf_t                 xm_buffer_nxt;
  logic       [ASIZE:0]    xm_bufend_r;
  logic       [ASIZE:0]    xm_bufend_nxt;
  // Offsets
  xm_offset_t [5:0]        xm_offsets_r;
  xm_offset_t [5:0]        xm_offsets_nxt;
  logic                    xm_buffer_en;


  logic                    xm_boost_r;
  logic                    xm_boost_nxt;

  logic [1:0]              xm_ost_cfg_r;
  logic [1:0]              xm_ost_cfg_nxt;

  // repack iters to skip continuely burst
  offset_t [5:0]           packed_iters_r;
  offset_t [5:0]           packed_iters_nxt;
  logic    [5:0]           packed_iters_en;

  // full burst length
  logic [31:0]             full_burst_r;
  logic                    full_burst_en;

  // rest burst length
  logic [31:0]             rest_burst_r;
  logic [31:0]             rest_burst_nxt;
  logic                    rest_burst_en;

  // burst length
  logic [31:0]             len_r;
  logic [31:0]             len_nxt;
  logic                    len_en;

  // total size
  logic [31:0]             total_size_r;
  logic [31:0]             total_size_nxt;
  logic                    total_size_en;

  // Iteration Next Flag
  logic                    nxt_iter_r;
  logic                    nxt_iter_nxt;
  logic                    nxt_iter_en;

  // Iter Next Offsets
  xm_offset_t              nxt_iter_oft_r;
  xm_offset_t              nxt_iter_oft_nxt;
  xm_offset_t              nxt_iter_oftb_r;
  xm_offset_t              nxt_iter_oftb_nxt;
  logic                    nxt_iter_oft_en;

  logic                    lst_issued;
  logic                    f;

  function automatic logic gen_axi_cmd(
                                       input  logic    [31:0]    ful_len,  // full burst length
                                       input  logic    [31:0]    cur_len,  // remaining burst length
                                       input  logic    [ASIZE:0] bufend,   // end of buffer + 1
                                       input  xm_ptr_t           ptr,      // running pointer
                                       output logic    [31:0]    len,      // length of current burst
                                       output logic    [31:0]    nxt_len   // length of next burst
                                      );
    // check fm request length hit wrap-back 
    // check for burst length and remaining burst
    logic              sf;
    sf = (({1'b0,ptr} + {1'b0,cur_len}) >= bufend) ? 1'b0 : 1'b1;
    if (sf) 
    begin
      len     = cur_len;
      nxt_len = ful_len;
    end
// spyglass disable_block W164a
//SMD:Width missmatch
//SJ :no overflow and ignore
    else 
    begin
      len     = bufend[ASIZE-1:0] - ptr - 1'b1;
      nxt_len = cur_len - len;
    end
// spyglass enable_block W164a
    return sf;
  endfunction : gen_axi_cmd


  // simple assignments
  assign xm_buffer_nxt   = hlapi_i_seq.buffer;
  assign xm_bufend_nxt   = {1'b0,hlapi_i_seq.buffer.base} + {1'b0,hlapi_i_seq.buffer.len} + 'd1;
  assign xm_offsets_nxt  = hlapi_i_seq.offsets;
  assign xm_boost_nxt    = hlapi_i_seq.boost;
  assign xm_ost_cfg_nxt  = hlapi_i_seq.ost_cfg;
  assign xm_request.base = xm_ptr_r;
  assign xm_request.len  = len_r;
  assign xm_request.padm = '0;
  assign xm_in_shp       = packed_iters_r;
  assign xm_it_check_nxt = xm_it_check_r == '0 ? 'd5 : xm_it_check_r - 'd1;
  assign lst_issued      = xm_accept & nxt_iter_r & (&xm_it_last);
  
  always_comb
  begin : xm_ptr_upd_PROC
    xm_offset_t o;
    o = '0;
    xm_ptr_nxt = '0;
    casez (nxt_iter_r)
    1'b1:
      begin
        // next dimension
        o |= nxt_iter_oftb_r; // len_r + nxt_iter_oft_r - 'd1;
      end
    default:
      begin
        // continue current burst
        o |= len_r;
      end
    endcase // casez (nxt_iter_r)
    if (xm_agu_state_r == xm_agu_state_idle_e)
    begin
      // new transaction
      xm_ptr_nxt |= hlapi_i_seq.ptr[ASIZE-1:0];
    end
    else
    begin
      // continue existing transaction
      xm_ptr_nxt |= incr_xm(xm_ptr_r[NPU_AXI_ADDR_W-1:0], o, xm_buffer_r);
    end
  end : xm_ptr_upd_PROC
  
// spyglass disable_block W164a
// SMD: Width Mismatch 
// SJ: Calculation will wrap, range limited 
  always_comb
  begin : xm_agu_issue_PROC // {
    logic [31:0] lenn;
    logic [31:0] rbn;
    xm_ptr_en         = 1'b0;
    xm_buffer_en      = 1'b0;
    xm_it_check_en    = 1'b0;
    packed_iters_nxt  = '0;
    packed_iters_en   = 6'b0;
    xm_valid          = 1'b0;
    xm_it_ack         = 1'b0;
    full_burst_en     = 1'b0;
    rest_burst_nxt    = '0;
    rest_burst_en     = 1'b0;
    cont_nxt          = 1'b0;
    len_nxt           = '0;
    len_en            = 1'b0;
    nxt_iter_en       = 1'b0;
    nxt_iter_oft_nxt  = '0;
    nxt_iter_oft_en   = 1'b0;
    total_size_nxt    = '0;
    total_size_en     = 1'b0;
    f                 = 1'b0;

    // precompute next address
    nxt_iter_nxt      = gen_axi_cmd(full_burst_r, rest_burst_r, xm_bufend_r, xm_ptr_r, lenn, rbn);
    // precompute next iteration offset
    for (int n = 5; n >= 0; n--)
    begin
      // looking for offsets
      if ((~xm_it_last[n]) & (~f)) 
      begin
        nxt_iter_oft_nxt |= xm_offsets_r[n];
        f                 = 1'b1;
      end
    end
    nxt_iter_oftb_nxt = nxt_iter_oft_nxt + rest_burst_r - 'd1;

    // Execute iteration
    case (xm_agu_state_r)
    xm_agu_state_idle_e:
      begin
        total_size_nxt   |= 'd1;
        packed_iters_nxt |= hlapi_i_seq.iter;
        xm_ptr_en         = hlapi_i_valid;
        xm_buffer_en      = hlapi_i_valid;
        packed_iters_en   = {6{hlapi_i_valid}};
        total_size_en     = hlapi_i_valid;
        full_burst_en     = hlapi_i_valid;
      end
    xm_agu_state_cal_e:
      begin
        logic [15:0] m;
// spyglass disable_block W164a W486 W164b
//SMD:RHS shift output is more than LHS Width
//SJ :intentional, msb need to be dropped
        m                 = packed_iters_r >> {xm_it_check_r,4'h0};
// spyglass enable_block W164a W164b W486
        xm_it_check_en    =  1'b1;
        packed_iters_nxt |= {6{16'd1}};
        // extend burst if offset is 1
        cont_nxt         |= cont_r & (((xm_offsets_r>>{xm_it_check_r,5'b0}) & 32'hFFFFFFFF) == 'd1);
        full_burst_en     = cont_nxt;
        // update iterators if burst is extended
        packed_iters_en  |= {5'd0,cont_nxt}<<xm_it_check_r;
        cont_nxt         |= xm_it_check_r == 3'd0;
        total_size_en     = 1'b1;
        total_size_nxt   |= total_size_r * m;
      end
    xm_agu_state_req_e:
      begin
        // Set Remaining Burst Length to Full burst
        rest_burst_nxt   |=  full_burst_r;
        rest_burst_en     =  xm_in_ack;
      end
    xm_agu_state_gen_e:
      begin
        // Generate Command
        nxt_iter_en       = 1'b1;
        nxt_iter_oft_en   = nxt_iter_nxt;
        rest_burst_nxt   |= rbn;
        len_nxt          |= lenn;
        len_en            = 1'b1;
        rest_burst_en     = 1'b1;
      end
    default: // xm_agu_state_issue_e:
      begin
        xm_valid        = 1'b1;
        if (xm_accept)
        begin
          xm_it_ack     = nxt_iter_r;
          xm_ptr_en     = 1'b1;
        end
      end
    endcase // case (xm_agu_state_r)
  end : xm_agu_issue_PROC // }
// spyglass enable_block W164a

  //
  // xm AGU next state
  //
  // xm AGU state and AXI master outputs
  // outputs: 
  always_comb
  begin : xm_agu_nxt_PROC
    hlapi_i_accept      = 1'b0;
    xm_in_req           = 1'b0;
    xm_agu_state_en     = 1'b0;
    xm_agu_state_nxt    = xm_agu_state_idle_e;
    casez (xm_agu_state_r)
      xm_agu_state_cal_e:
        begin
          xm_agu_state_nxt = xm_agu_state_req_e;
          xm_agu_state_en  = xm_it_check_r == 3'h0;
        end
      xm_agu_state_req_e:
        begin
          // Keep assert Iteration issue
          xm_in_req        = 1'b1;
          xm_agu_state_nxt = xm_agu_state_gen_e;
          xm_agu_state_en  = xm_in_ack;
        end
      xm_agu_state_gen_e:
        begin
          xm_agu_state_en  = 1'b1;
          xm_agu_state_nxt = xm_agu_state_issue_e;
        end
      xm_agu_state_issue_e:
        begin
          if (lst_issued) 
          begin
            xm_agu_state_en  = 1'b1;
            xm_agu_state_nxt = xm_agu_state_idle_e;
          end
          else if (xm_accept) 
          begin
            xm_agu_state_en  = 1'b1;
            xm_agu_state_nxt = xm_agu_state_gen_e;
          end
        end
      default: // xm_agu_state_idle_e
        begin
          // idle, wait for next request
          hlapi_i_accept   = 1'b1;
          xm_agu_state_en  = hlapi_i_valid;
          xm_agu_state_nxt = xm_agu_state_cal_e;
        end
    endcase // casez (xm_agu_state_r)
  end : xm_agu_nxt_PROC

  //
  // FSM 
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_PROC
    if (rst_a == 1'b1)
    begin
      xm_agu_state_r <= xm_agu_state_idle_e;
    end
    else if (xm_agu_state_en)
    begin
      xm_agu_state_r <= xm_agu_state_nxt;
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
      xm_ptr_r         <= 'b0;
      xm_buffer_r      <= 'b0;
      xm_bufend_r      <= 'b0;
      xm_offsets_r     <= 'b0;
      xm_boost_r       <= 'b0;
      xm_ost_cfg_r     <= 'b0;
      packed_iters_r   <= 'b0;
      full_burst_r     <= 'b0;
      rest_burst_r     <= 'b0;
      cont_r           <= 'b1;
      len_r            <= 'b0;
      nxt_iter_r       <= 'b0;
      nxt_iter_oft_r   <= 'b0;
      nxt_iter_oftb_r  <= 'b0;
      total_size_r     <= 'b0;
      xm_it_check_r    <= 'h5;
    end
    else 
    begin
      if (xm_ptr_en)
      begin
        xm_ptr_r       <= xm_ptr_nxt;
      end
      if (xm_buffer_en)
      begin
        xm_buffer_r    <= xm_buffer_nxt;
        xm_bufend_r    <= xm_bufend_nxt;
        xm_offsets_r   <= xm_offsets_nxt;
        xm_boost_r     <= xm_boost_nxt;
        xm_ost_cfg_r   <= xm_ost_cfg_nxt;
      end
      if (len_en)
      begin
        len_r          <= len_nxt;
      end
      for (int i = 0; i < 6; i++)
      begin     
        if (packed_iters_en[i])
        begin
          packed_iters_r[i] <= packed_iters_nxt[i];
        end
      end
      if (total_size_en)
      begin
        total_size_r   <= total_size_nxt;
      end
      if (full_burst_en)
      begin
        full_burst_r   <= total_size_nxt;
      end
      if (rest_burst_en)
      begin
        rest_burst_r   <= rest_burst_nxt;
      end
      if (nxt_iter_en)
      begin
        nxt_iter_r     <= nxt_iter_nxt;
      end
      if (nxt_iter_oft_en)
      begin
        nxt_iter_oft_r  <= nxt_iter_oft_nxt;
        nxt_iter_oftb_r <= nxt_iter_oftb_nxt;
      end
      if (xm_it_check_en)
      begin
        xm_it_check_r  <= xm_it_check_nxt;
        cont_r         <= cont_nxt;
      end
    end
  end : reg_pipe_PROC
  
  //Output assign
  assign idle         = (xm_agu_state_r == xm_agu_state_idle_e);
  assign xm_len_trans = total_size_r;
  assign boost        = xm_boost_r;
  assign ost_cfg      = xm_ost_cfg_r;

endmodule : npu_stu_xm_agu
