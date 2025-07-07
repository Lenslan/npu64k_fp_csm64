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
// Top-level file for the FM AGU for decompress
//

 
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"

module npu_idma_fm_dcp_agu
  import npu_types::*;
(
   input  logic            clk,      // clock
   input  logic            rst_a,    // asynchronous reset, active high
// spyglass disable_block W240
// SMD: Declare but Not used 
// SJ: Ignore 
   // New descr issue
   input  logic            hlapi_i_valid,   // start new iteration
   output logic            hlapi_i_accept,  // acknowledge start
   input  hlapi_xm_agu_t   hlapi_i_seq,     // AGU params 
   input  logic            hlapi_i_init,    // iDMA VM init mode enable 
   input  logic            hlapi_i_gather,  // iDMA Gather load enable 
   input  logic   [31:0]   hlapi_i_bc,      // iDMA B-DMA flag 

   // Iterations
   output logic            fm_in_req,       // start new iteration
   input  logic            fm_in_ack,       // acknowledge start
   output offset_t [5:0]   fm_in_shp,       // shape of the iterator
   input  logic            fm_it_req,       // iterator valid
   output logic            fm_it_ack,       // iterator accept
   input  logic    [5:0]   fm_it_first,     // first bits
   input  logic    [5:0]   fm_it_last,      // last bits
// spyglass enable_block W240

   // Meta Load
   output logic            meta_rd_accept,
   output logic [$clog2(DMA_VM_LANES*ISIZE)-1:0]      meta_rd_num,
   output logic [$clog2(DMA_VM_LANES*ISIZE)-1:0]      meta_rd_alsb,
   input  logic [DMA_VM_LANES*8*ISIZE-1:0]    meta_rd_data,
   input  logic [15:0]     meta_vld_size,

   // Gather VM load
   input  gidx_t [1:0]     gather_idx, //{idh8,idw8}
   input  logic            gather_valid,
   output logic            gather_accept,

   // fm status
   output logic [31:0]     fm_len_trans,
   // fm request
   output logic            fm_valid,
   output xm_buf_t         fm_request,
   input  logic            fm_accept,
   output logic            boost,
   output logic [1:0]      rd_ost,
   output logic [7:0]      bc_flags,

   //IDLE
   output logic            idle
);

  // Local parameters
  typedef enum logic [2:0] { 
    fm_agu_state_idle_e,  // issue state is idle
    fm_agu_state_cal_e,   // calculation ful burst & alternative iteration
    fm_agu_state_req_e,   // request iteration 
    fm_agu_state_gen_e,   // generate fm command seq 
    fm_agu_state_gal_e,   // Reload Gather PTR
    fm_agu_state_issue_e  // issue the fm seq 
  } fm_agu_state_t;

  // Internal signals
  fm_agu_state_t           fm_agu_state_r;
  fm_agu_state_t           fm_agu_state_nxt;
  logic                    fm_agu_state_en;

  // Iteration Check Flag
  logic    [2:0]           fm_it_check_r;
  logic    [2:0]           fm_it_check_nxt;
  logic                    fm_it_check_en;

  // burst ptr
  xm_ptr_t                 fm_ptr_r;
  xm_ptr_t                 fm_ptr_nxt;
  logic                    fm_ptr_en;

  logic                    fm_compress_r;
  logic                    fm_compress_nxt;

  logic                    fm_boost_r;
  logic                    fm_boost_nxt;

  logic [1:0]              fm_rd_ost_r;
  logic [1:0]              fm_rd_ost_nxt;
  logic [7:0]              fm_bc_flgs_r;
  logic [7:0]              fm_bc_flgs_nxt;

  logic                    fm_gather_r;
  logic                    fm_gather_nxt;

  xm_ptr_t                 fm_gptr_r;
  xm_ptr_t                 fm_gptr_nxt;
  logic                    fm_gptr_en;

  // buffer ptr
  xm_buf_t                 fm_buffer_r;
  xm_buf_t                 fm_buffer_nxt;
  logic                    fm_buffer_en;
  logic       [ASIZE:0]    fm_bufend_r;
  logic       [ASIZE:0]    fm_bufend_nxt;

  // Offsets
  xm_offset_t [5:0]        fm_offsets_r;
  xm_offset_t [5:0]        fm_offsets_nxt;

  xm_offset_t              idw8_offsets_nxt;
  xm_offset_t              idw8_offsets_r;

  xm_offset_t              idh8_offsets_nxt;
  xm_offset_t              idh8_offsets_r;

  xm_offset_t              gather_offs;

  // repack iters to skip continuely burst
  offset_t [5:0]           packed_iters_r;
  offset_t [5:0]           packed_iters_nxt;
  logic    [5:0]           packed_iters_en;

  // Continue Flag
  logic                    cont_r;
  logic                    cont_nxt;

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
  assign fm_buffer_nxt   = hlapi_i_seq.buffer;
  assign fm_bufend_nxt   = {1'b0,hlapi_i_seq.buffer.base} + {1'b0,hlapi_i_seq.buffer.len} + 'd1;
  assign fm_compress_nxt = 1'b0;
  assign fm_boost_nxt    = hlapi_i_seq.boost[0];
  assign fm_rd_ost_nxt   = hlapi_i_seq.rd_ost;
  assign fm_bc_flgs_nxt  = hlapi_i_bc[7:0];
  assign fm_gather_nxt   = hlapi_i_gather;
  assign fm_request.base = fm_ptr_r;
  assign fm_request.padm = '0;
  assign fm_request.len  = len_r;
  assign fm_in_shp       = packed_iters_r;
  assign fm_it_check_nxt = fm_it_check_r == '0 ? 'd5 : fm_it_check_r - 'd1;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
  assign gather_offs     = (gather_idx[0] * idw8_offsets_r) + (gather_idx[1] * idh8_offsets_r);
// spyglass enable_block W164a


  always_comb
  begin : fm_ptr_upd_PROC
    xm_offset_t o;
    o = '0;
    fm_ptr_nxt   = '0;
    fm_gptr_nxt  = '0;
    casez ({fm_compress_r,nxt_iter_r})
    2'b01:
      begin
        // next dimension
        o |= nxt_iter_oftb_r; // len_r + nxt_iter_oft_r - 'd1;
      end
    default:
      begin
        // continue current burst
        o |= len_r;
      end
    endcase // casez ({fm_compress_r,nxt_iter_r})
    case (fm_agu_state_r)
    fm_agu_state_idle_e:
      begin
        // new transaction
        fm_ptr_nxt  |= hlapi_i_seq.ptr[ASIZE-1:0];
        fm_gptr_nxt |= hlapi_i_seq.ptr[ASIZE-1:0];
      end
    fm_agu_state_gal_e:
      begin
        // next pointer for gather transaction
        fm_ptr_nxt  |= fm_gptr_r + gather_offs;
      end
    default:
      begin
        fm_ptr_nxt  |= incr_xm(fm_ptr_r[NPU_AXI_ADDR_W-1:0], o, fm_buffer_r);
      end
    endcase // case (fm_agu_state_r)
  end : fm_ptr_upd_PROC


// spyglass disable_block W164a
// SMD: Width Mismatch 
// SJ: Calculation will wrap, range limited 
  always_comb
  begin : fm_agu_issue_PROC // {
    logic [31:0] lenn;
    logic [31:0] rbn;
    fm_ptr_en         = 1'b0;
    fm_gptr_en        = 1'b0;
    fm_buffer_en      = 1'b0;
    fm_it_check_en    = 1'b0;
    packed_iters_nxt  = '0;
    packed_iters_en   = '0;
    fm_valid          = 1'b0;
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
    lst_issued        = 1'b0;
    f                 = 1'b0;
    fm_it_ack         = 1'b0;
    fm_offsets_nxt    = '0;
    idw8_offsets_nxt  = '0;
    idh8_offsets_nxt  = '0;

    // precompute next address
    nxt_iter_nxt      = fm_compress_r | gen_axi_cmd(full_burst_r, rest_burst_r, fm_bufend_r, fm_ptr_r, lenn, rbn);
    // Search for Next Iter offsets
    for (int n = 5; n >= 0; n--)
    begin
      // looking for offsets
      if ((~fm_it_last[n]) & (~f)) 
      begin
        nxt_iter_oft_nxt |= fm_offsets_r[n];
        f                 = 1'b1;
      end
    end
    nxt_iter_oftb_nxt = nxt_iter_oft_nxt + rest_burst_r - 'd1;

    // Execute iteration
    case (fm_agu_state_r)
    fm_agu_state_idle_e:
      begin
        if (hlapi_i_gather)
        begin
          fm_offsets_nxt     |= hlapi_i_seq.offsets;
          packed_iters_nxt   |= hlapi_i_seq.iter;
          //Reuse the iter number to help generate but not offset ptr by AGU.
          idw8_offsets_nxt   |= hlapi_i_seq.offsets[1];
          idh8_offsets_nxt   |= hlapi_i_seq.offsets[0];
          packed_iters_nxt[2] = 8;
          fm_offsets_nxt[0]  = '0;
          fm_offsets_nxt[1]  = '0;
          fm_offsets_nxt[2]  = '0;
        end
        else
        begin
          fm_offsets_nxt   |= hlapi_i_seq.offsets;
          packed_iters_nxt |= hlapi_i_seq.iter;
        end
        total_size_nxt   |= hlapi_i_seq.compress ? 'd0 : 'd1;
        fm_ptr_en         = hlapi_i_valid;
        fm_gptr_en        = hlapi_i_valid;
        fm_buffer_en      = hlapi_i_valid;
        packed_iters_en   = {6{hlapi_i_valid}};
        total_size_en     = hlapi_i_valid;
        full_burst_en     = hlapi_i_valid;
      end
    fm_agu_state_cal_e:
      begin
        logic [15:0] m;
// spyglass disable_block W164a W486 W164b
//SMD:RHS shift output is more than LHS Width
//SJ :intentional, msb need to be dropped
        m                 = packed_iters_r >> {fm_it_check_r,4'h0};
// spyglass enable_block W164a W164b W486
        fm_it_check_en    = 1'b1;
        packed_iters_nxt |= {6{16'd1}};
        // extend burst if offset is 1
        cont_nxt         |= cont_r & (((fm_offsets_r>>{fm_it_check_r,5'b0}) & 32'hFFFFFFFF) == 'd1);
        full_burst_en     = cont_nxt;
        // update iterators if burst is extended
        packed_iters_en  |= {5'd0,cont_nxt}<<fm_it_check_r;
        cont_nxt         |= fm_it_check_r == 3'd0;
        total_size_en     = 1'b1;
        total_size_nxt   |= total_size_r * m;
      end
    fm_agu_state_req_e:
      begin
        // Set Remaining Burst Length to Full burst
        rest_burst_nxt      |= full_burst_r;
        rest_burst_en        = fm_in_ack;
      end
    fm_agu_state_gen_e:
      begin
        nxt_iter_en         = 1'b1;
        begin
          // Generate Normal Command
          len_nxt          |= lenn;
          rest_burst_nxt   |=  rbn;
          rest_burst_en     = 1'b1;
          len_en            = 1'b1;
        end
        nxt_iter_oft_en = nxt_iter_nxt;
      end
    fm_agu_state_gal_e:
      begin
        fm_ptr_en         = 1'b1;
      end
    default: // fm_agu_state_issue_e
      begin
        fm_valid           = 1'b1;
        total_size_nxt    |= total_size_r + len_r;
        if (fm_accept) 
        begin
          begin
            fm_it_ack      = nxt_iter_r;
            fm_ptr_en      = 1'b1;
          end
          lst_issued       = nxt_iter_r & (&fm_it_last);
        end
      end
    endcase // case (fm_agu_state_r)
  end : fm_agu_issue_PROC // }
// spyglass enable_block W164a

  //
  // fm AGU next state
  //
  // fm AGU state and AXI master outputs
  // outputs: 
  always_comb
  begin : fm_agu_nxt_PROC
    hlapi_i_accept      = 1'b0;
    fm_in_req           = 1'b0;
    fm_agu_state_en     = 1'b0;
    fm_agu_state_nxt    = fm_agu_state_r;
    meta_rd_accept      = 1'b0;
    gather_accept       = 1'b0;
    casez (fm_agu_state_r)
    fm_agu_state_cal_e:
      begin
        fm_agu_state_nxt = fm_agu_state_req_e;
        fm_agu_state_en  = fm_it_check_r == 3'h0;
      end
    fm_agu_state_req_e:
      begin
        // Keep assert Iteration issue
        fm_in_req        = 1'b1;
        fm_agu_state_nxt = (fm_gather_r == 1'b1) ? fm_agu_state_gal_e : fm_agu_state_gen_e;
        fm_agu_state_en  = fm_in_ack;
      end
    fm_agu_state_gal_e:
      begin
        fm_agu_state_en  = gather_valid;
        fm_agu_state_nxt = fm_agu_state_gen_e;
      end
    fm_agu_state_gen_e:
      begin
        if (((fm_compress_r == 1'b1) && (meta_vld_size > 16'h0)) || 
            ((fm_gather_r   == 1'b1) && (gather_valid))          ||
            ((fm_compress_r == 1'b0) && (fm_gather_r== 1'b0)) 
            )
        begin
          // Jump to Issue when Metadata is read or non-compress mode
          fm_agu_state_en  = 1'b1;
          fm_agu_state_nxt = fm_agu_state_issue_e;
        end
      end
    fm_agu_state_issue_e:
      begin
        if (lst_issued) begin
          fm_agu_state_en  = 1'b1;
          fm_agu_state_nxt = fm_agu_state_idle_e;
          gather_accept    = fm_gather_r;
        end
        else if (fm_accept) begin
          fm_agu_state_en  = 1'b1;
          // Only reload gather ptr when current burst is fully sent
          fm_agu_state_nxt = ((fm_gather_r == 1'b1) & nxt_iter_r & (&fm_it_last[5:3])) ? fm_agu_state_gal_e 
                                                                                       : fm_agu_state_gen_e;
          if ((fm_gather_r == 1'b1) & nxt_iter_r & (&fm_it_last[5:3]))
          begin
            // Update Gather Idx When Last C0/C1/C2
            gather_accept    = 1'b1;
          end
        end
      end
    default: // fm_agu_state_idle_e
      begin
        // idle, wait for next request
        hlapi_i_accept   = 1'b1;
        fm_agu_state_en  = hlapi_i_valid & (~hlapi_i_init);
        if (hlapi_i_seq.compress) 
        begin
          // Compress Enabled, Skip Iteration Alter 
          fm_agu_state_nxt = fm_agu_state_req_e;
        end
        else 
        begin
          // Normal Enabled, Calculate FM Iter
          fm_agu_state_nxt = fm_agu_state_cal_e;
        end
      end
    endcase // casez (fm_agu_state_r)
  end : fm_agu_nxt_PROC

  //
  // FSM 
  //
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_PROC
    if (rst_a == 1'b1)
    begin
      fm_agu_state_r <= fm_agu_state_idle_e;
    end
    else if (fm_agu_state_en)
    begin
      fm_agu_state_r <= fm_agu_state_nxt;
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
      fm_ptr_r         <= 'b0;
      fm_buffer_r      <= 'b0;
      fm_bufend_r      <= 'b0;
      fm_offsets_r     <= 'b0;
      idh8_offsets_r   <= 'b0;
      idw8_offsets_r   <= 'b0;
      packed_iters_r   <= 'b0;
      full_burst_r     <= 'b0;
      rest_burst_r     <= 'b0;
      cont_r           <= 'b1;
      len_r            <= 'b0;
      nxt_iter_r       <= 'b0;
      nxt_iter_oft_r   <= 'b0;
      nxt_iter_oftb_r  <= 'b0;
      total_size_r     <= 'b0;
      fm_it_check_r    <= 'h5;
      fm_compress_r    <= 'b0;
      fm_boost_r       <= 'b0;
      fm_rd_ost_r      <= 'b0;
      fm_gather_r      <= 'b0;
      fm_gptr_r        <= 'b0;
      fm_bc_flgs_r     <= 'b0;
    end
    else begin
      if (fm_ptr_en)
      begin
        // running pointer
        fm_ptr_r       <= fm_ptr_nxt;
      end
      if (fm_gptr_en)
      begin
        // gather base pointer
        fm_gptr_r       <= fm_gptr_nxt;
      end
      if (fm_buffer_en)
      begin
        // static signals
        fm_buffer_r    <= fm_buffer_nxt;
        fm_bufend_r    <= fm_bufend_nxt;
        fm_offsets_r   <= fm_offsets_nxt;
        idh8_offsets_r <= idh8_offsets_nxt;
        idw8_offsets_r <= idw8_offsets_nxt;
        fm_compress_r  <= fm_compress_nxt;
        fm_boost_r     <= fm_boost_nxt;
        fm_rd_ost_r    <= fm_rd_ost_nxt;
        fm_bc_flgs_r   <= fm_bc_flgs_nxt;
        fm_gather_r    <= fm_gather_nxt;
      end
      for (int i = 0; i < 6; i++)
      begin     
        if (packed_iters_en[i])
        begin
          packed_iters_r[i] <= packed_iters_nxt[i];
        end
      end
      if (full_burst_en)
      begin
        full_burst_r   <= total_size_nxt;
      end
      if (rest_burst_en)
      begin
        rest_burst_r   <= rest_burst_nxt;
      end
      if (len_en)
      begin
        len_r          <= len_nxt;
      end
      if (nxt_iter_en)
      begin
        nxt_iter_r     <= nxt_iter_nxt;
      end
      if (nxt_iter_oft_en)
      begin
        nxt_iter_oftb_r <= nxt_iter_oftb_nxt;
      end
      if (total_size_en)
      begin
        total_size_r   <= total_size_nxt;
      end
      if (fm_it_check_en)
      begin
        fm_it_check_r  <= fm_it_check_nxt;
        cont_r         <= cont_nxt;
      end
    end
  end : reg_pipe_PROC
  
  //Output assign
  assign idle         = (fm_agu_state_r == fm_agu_state_idle_e);
  assign fm_len_trans = total_size_r;

  assign meta_rd_num  = 6'h0;
  assign meta_rd_alsb = 6'h0;
  assign boost        = fm_boost_r;
  assign rd_ost       = fm_rd_ost_r;
  assign bc_flags     = fm_bc_flgs_r;
endmodule : npu_idma_fm_dcp_agu
